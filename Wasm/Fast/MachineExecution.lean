import Wasm.Fast.MachineDispatch

namespace Wasm.Fast.Machine

structure Change where
  next : Machine
  heap : StructChange := .unchanged

def Change.commit (change : Change) : Machine :=
  {change.next with store := change.heap.apply change.next.store}

private def afterLocal (m : Machine) (below : List Value) (tail : List AdminInstr) :
    RedexPlan → Change
  | .ready next => ⟨⟨next.store, next.frame, next.code ++ tail, below, m.contexts⟩, .unchanged⟩
  | .structures change code =>
    ⟨⟨m.store, m.frame, code ++ tail, below, m.contexts⟩, change⟩

private theorem afterLocal_decode (m : Machine) (below : List Value) (tail code : List AdminInstr)
    (plan : RedexPlan) :
    (afterLocal m below tail plan).commit.toConfiguration =
      plug m.contexts ⟨(plan.apply ⟨m.store, m.frame, code⟩).store,
        (plan.apply ⟨m.store, m.frame, code⟩).frame,
        values below.reverse ++ (plan.apply ⟨m.store, m.frame, code⟩).code ++ tail⟩ := by
  cases plan <;> simp [afterLocal, Change.commit, toConfiguration, active,
    RedexPlan.apply, StructChange.apply, List.append_assoc]

abbrev CheckedChange (m : Machine) :=
  Option {change : Change // ConfigStep m.toConfiguration change.commit.toConfiguration}

private def localChange (m : Machine) : CheckedChange m := by
  match hc : m.code with
  | [] => exact none
  | head :: tail =>
    match hn : operandCount m.store m.frame head with
    | some count =>
      let top := m.operands.take count
      let below := m.operands.drop count
      let redex : Configuration := ⟨m.store, m.frame, values top.reverse ++ [head]⟩
      match hd : dispatch head redex with
      | none => exact none
      | some result =>
        exact some ⟨afterLocal m below tail result.val, by
          rw [afterLocal_decode m below tail redex.code]
          have split : m.operands.reverse = below.reverse ++ top.reverse := by
            simp [top, below]
          have step := plugStep m.contexts (inValues result.property below.reverse tail)
          simpa [toConfiguration, active, redex, hc, split, values, List.map_append,
            List.append_assoc] using step⟩
    | none =>
      match head with
      | .trap | .throwing _ =>
        match hd : dispatch head m.active with
        | none => exact none
        | some result =>
          exact some ⟨afterLocal m [] [] result.val, by
            rw [afterLocal_decode m [] [] m.active.code]
            simpa [toConfiguration, active, values] using plugStep m.contexts result.property⟩
      | _ => exact none

private def afterUnwind (m : Machine) (context : MachineContext)
    (rest : List MachineContext) : RedexPlan → Change
  | .ready next => ⟨⟨next.store, next.frame, next.code, [], rest⟩, .unchanged⟩
  | .structures change code =>
    ⟨⟨m.store, (context.wrap m.active).frame, code, [], rest⟩, change⟩

private theorem afterUnwind_decode (m : Machine) (context : MachineContext)
    (rest : List MachineContext) (plan : RedexPlan) :
    (afterUnwind m context rest plan).commit.toConfiguration =
      plug rest (plan.apply (context.wrap m.active)) := by
  cases plan <;> simp [afterUnwind, Change.commit, toConfiguration, active,
    RedexPlan.apply, StructChange.apply, MachineContext.wrap, values]

private def unwindChange (m : Machine) : CheckedChange m := by
  match hx : m.contexts with
  | [] => exact none
  | context :: rest =>
    match hd : unwind context m.code.head? (context.wrap m.active) with
    | none => exact none
    | some result =>
      exact some ⟨afterUnwind m context rest result.val, by
        rw [afterUnwind_decode]
        simpa [toConfiguration, hx, plug] using plugStep rest result.property⟩

def checkedChange (m : Machine) : CheckedChange m :=
  match localChange m with
  | some next => some next
  | none => unwindChange m

def step (m : Machine) : Option Machine :=
  (checkedChange (normalize m)).map fun change => change.val.commit

theorem step_spec (h : step m = some next) : Wasm.ConfigStep m.toSpec next.toSpec := by
  unfold step at h
  cases hs : checkedChange (normalize m) with
  | none => simp [hs] at h
  | some change =>
    simp [hs] at h
    subst next
    have sound : ConfigStep m.toConfiguration change.val.commit.toConfiguration := by
      simpa [normalize_same] using change.property
    exact sound.toSpec

private def checkedRun : (fuel : Nat) → (m : Machine) →
    {next : Machine // ConfigSteps m.toConfiguration next.toConfiguration}
  | 0, m => ⟨m, .refl⟩
  | fuel + 1, m =>
    let focused := normalize m
    match checkedChange focused with
    | none => ⟨focused, by rw [normalize_same]; exact .refl⟩
    | some change =>
      let result := checkedRun fuel change.val.commit
      ⟨result.val, .cons (by simpa [focused, normalize_same] using change.property)
        result.property⟩

structure RunResult where
  state : Machine
  status : RunStatus
  deriving BEq, Repr

private def terminalStatus (m : Machine) : RunStatus :=
  if !m.contexts.isEmpty then .stuck
  else match m.code with
    | [] => .finished m.operands.reverse
    | [.trap] => if m.operands.isEmpty then .trapped else .stuck
    | [.throwing address] => if m.operands.isEmpty then .exception address else .stuck
    | _ => .stuck

-- The semantic meaning of reported results, independently of the machine representation.
def StatusSpec (status : RunStatus) (c : Wasm.Configuration) : Prop :=
  match status with
  | .finished vs => c.code = values vs
  | .trapped => c.code = [.trap]
  | .exception address => c.code = [.throwing address]
  | .exhausted => ∃ next, Wasm.ConfigStep c next
  | .stuck => True
  | .callStackExhausted => False

private theorem terminalStatus_spec (m : Machine) : StatusSpec (terminalStatus m) m.toSpec := by
  cases hx : m.contexts with
  | cons context rest => simp [terminalStatus, hx, StatusSpec]
  | nil =>
    simp only [terminalStatus, hx, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    split
    all_goals try
      solve | simp_all [StatusSpec, toSpec, toConfiguration, plug, active,
        Configuration.toSpec]
    all_goals cases ho : m.operands <;>
      simp_all [StatusSpec, toSpec, toConfiguration, plug, active, Configuration.toSpec, values]

-- A probe plans a step but never commits a heap mutation.
def run (fuel : Nat) (m : Machine) : RunResult :=
  let final := (checkedRun fuel m).val
  let focused := normalize final
  let status := if (checkedChange focused).isSome then .exhausted else terminalStatus focused
  ⟨final, status⟩

theorem run_sound : ConfigSteps m.toConfiguration (run fuel m).state.toConfiguration :=
  (checkedRun fuel m).property

theorem run_spec :
    Wasm.ConfigSteps m.toSpec (run fuel m).state.toSpec := run_sound.toSpec

theorem run_status_spec : StatusSpec (run fuel m).status (run fuel m).state.toSpec := by
  unfold run
  simp only
  split
  · rename_i h
    cases hp : checkedChange (normalize (checkedRun fuel m).val) with
    | none => simp [hp] at h
    | some change =>
      refine ⟨change.val.commit.toSpec, ?_⟩
      have sound := change.property.toSpec
      simpa [toSpec, normalize_same] using sound
  · have sound := terminalStatus_spec (normalize (checkedRun fuel m).val)
    simpa [toSpec, normalize_same] using sound

end Wasm.Fast.Machine
