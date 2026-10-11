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

theorem step_sound (h : step m = some next) :
    ConfigStep m.toConfiguration next.toConfiguration := by
  unfold step at h
  cases hs : checkedChange (normalize m) with
  | none => simp [hs] at h
  | some change =>
    simp [hs] at h
    subst next
    have sound : ConfigStep m.toConfiguration change.val.commit.toConfiguration := by
      simpa [normalize_same] using change.property
    exact sound

theorem step_spec (h : step m = some next) : Wasm.ConfigStep m.toSpec next.toSpec :=
  (step_sound h).toSpec

-- Native instructions and resource policy extend this same machine loop.
structure PlannedStep where
  change : Change
  output : List Value := []

structure ExecutionHooks where
  fallback : Machine → Option PlannedStep := fun _ => none
  exceedsLimit : Machine → Bool := fun _ => false

@[specialize] def planWith (hooks : ExecutionHooks) (m : Machine) : Option PlannedStep :=
  match checkedChange m with
  | some change => some ⟨change.val, []⟩
  | none => hooks.fallback m

structure ExecutionResult where
  state : Machine
  output : List Value
  limitExceeded : Bool

-- Plan first, release the input, then commit; preserve array ownership on allocation.
@[specialize] def execute (hooks : ExecutionHooks) :
    Nat → Machine → List Value → ExecutionResult
  | 0, m, output => ⟨m, output, false⟩
  | fuel + 1, m, output =>
    let focused := normalize m
    if hooks.exceedsLimit focused then ⟨focused, output, true⟩
    else match checkedChange focused with
      | some change => execute hooks fuel change.val.commit output
      | none => match hooks.fallback focused with
        | none => ⟨focused, output, false⟩
        | some plan =>
          let output := if plan.output.isEmpty then output else output ++ plan.output
          execute hooks fuel plan.change.commit output

-- The common path avoids packaging a certified step as an extension result. This
-- equation proves the optimization has the same recurrence for every hook policy.
theorem execute_succ (hooks : ExecutionHooks) (fuel : Nat) (m : Machine)
    (output : List Value) :
    execute hooks (fuel + 1) m output =
      let focused := normalize m
      if hooks.exceedsLimit focused then ⟨focused, output, true⟩
      else match planWith hooks focused with
        | none => ⟨focused, output, false⟩
        | some plan =>
          let output := if plan.output.isEmpty then output else output ++ plan.output
          execute hooks fuel plan.change.commit output := by
  cases hc : checkedChange (normalize m) <;> simp [execute, planWith, hc]

private theorem execute_sound (fuel : Nat) (m : Machine) (output : List Value) :
    ConfigSteps m.toConfiguration (execute {} fuel m output).state.toConfiguration := by
  induction fuel generalizing m output with
  | zero => exact .refl
  | succ fuel ih =>
    cases hc : checkedChange (normalize m) with
    | none =>
      simpa [execute, hc, normalize_same] using
        (ConfigSteps.refl (config := m.toConfiguration))
    | some change =>
      have first : ConfigStep m.toConfiguration change.val.commit.toConfiguration := by
        simpa [normalize_same] using change.property
      simpa [execute, hc] using
        (ConfigSteps.cons first (ih change.val.commit output))

structure RunResult where
  state : Machine
  status : RunStatus
  deriving BEq, Repr

def terminalStatus (m : Machine) : RunStatus :=
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
  let final := (execute {} fuel m []).state
  let focused := normalize final
  let status := if (checkedChange focused).isSome then .exhausted else terminalStatus focused
  ⟨final, status⟩

theorem run_sound : ConfigSteps m.toConfiguration (run fuel m).state.toConfiguration :=
  execute_sound fuel m []

theorem run_spec :
    Wasm.ConfigSteps m.toSpec (run fuel m).state.toSpec := run_sound.toSpec

theorem run_status_spec : StatusSpec (run fuel m).status (run fuel m).state.toSpec := by
  unfold run
  simp only
  split
  · rename_i h
    cases hp : checkedChange (normalize (execute {} fuel m []).state) with
    | none => simp [hp] at h
    | some change =>
      refine ⟨change.val.commit.toSpec, ?_⟩
      have sound := change.property.toSpec
      simpa [toSpec, normalize_same] using sound
  · have sound := terminalStatus_spec (normalize (execute {} fuel m []).state)
    simpa [toSpec, normalize_same] using sound

end Wasm.Fast.Machine
