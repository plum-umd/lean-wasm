import Wasm.ControlChoice

/-!
Executable stepping of the supported fragment. Each internal result carries a proof
of its `ExecStep`; proofs are erased by Lean's compiler. The public API returns plain
instruction sequences. Scanning operand values is bookkeeping, not a semantic step.
-/

namespace Wasm

open AdminInstr Instr

private abbrev CheckedStep (types : TypeContext) (es : List AdminInstr) :=
  Option { next : List AdminInstr // ExecStep types es next }

private structure ValuePrefix (es : List AdminInstr) where
  stack : List Value
  rest : List AdminInstr
  reconstruct : es = values stack ++ rest

private def splitValues : (es : List AdminInstr) → ValuePrefix es
  | instr (.const v) :: tail =>
      let p := splitValues tail
      ⟨v :: p.stack, p.rest, by simp [values, p.reconstruct]⟩
  | es => ⟨[], es, rfl⟩

private structure Operands (stack : List Value) (n : Nat) where
  below : List Value
  args : List Value
  reconstruct : stack = below ++ args
  arity : args.length = n

/-- Split off the top n operands, preserving their specification order. -/
private def operands (stack : List Value) (n : Nat) : Option (Operands stack n) :=
  if h : n ≤ stack.length then
    some ⟨stack.take (stack.length - n), stack.drop (stack.length - n),
      (List.take_append_drop _ _).symm, by simp; omega⟩
  else none

private def inContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedStep types es) : CheckedStep types (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

private def localStep (types : TypeContext) (es : List AdminInstr) : CheckedStep types es :=
  match h : reduce es with
  | some next => some ⟨next, .primitive (reduce_sound h)⟩
  | none =>
    match h : reduceInteger es with
    | some next => some ⟨next, .integer (reduceInteger_sound h)⟩
    | none =>
      match h : reduceControlChoice es with
      | some next => some ⟨next, .control (reduceControlChoice_sound h)⟩
      | none => none

private def fixedArity : Instr → Option Nat
  | .nop | .unreachable => some 0
  | .drop | .eqz _ | .if_ _ _ _ | .brIf _ | .brTable _ _
    | .intUnary _ _ | .intConvert _ => some 1
  | .binop _ _ | .intBinary _ _ | .intRel _ _ => some 2
  | .select _ => some 3
  | _ => none

private def focusStep (types : TypeContext) (stack : List Value) (i : Instr) :
    CheckedStep types (values stack ++ [instr i]) := by
  match i with
  | .block bt body =>
    match ht : bt.resolve types with
    | none => exact none
    | some ft =>
      match operands stack ft.params.length with
      | none => exact none
      | some p =>
        exact some ⟨values p.below ++
          [.label ft.results.length [] (values p.args ++ instructions body)], by
          simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
            (ExecStep.context (vs := p.below) (tail := [])
              (.control (.block ht p.arity)))⟩
  | .loop bt body =>
    match ht : bt.resolve types with
    | none => exact none
    | some ft =>
      match operands stack ft.params.length with
      | none => exact none
      | some p =>
        exact some ⟨values p.below ++
          [.label ft.params.length [.loop bt body] (values p.args ++ instructions body)], by
          simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
            (ExecStep.context (vs := p.below) (tail := [])
              (.control (.loop ht p.arity)))⟩
  | i =>
    match fixedArity i with
    | none => exact none
    | some n =>
      match operands stack n with
      | none => exact none
      | some p =>
        simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
          inContext p.below [] (localStep types (values p.args ++ [instr i]))

private def labelStep (types : TypeContext) (n : Nat) (continuation : List Instr)
    (body : List AdminInstr) (inner : CheckedStep types body) :
    CheckedStep types [.label n continuation body] := by
  let p := splitValues body
  match hr : p.rest with
  | [] =>
    exact some ⟨values p.stack, by
      simpa [p.reconstruct, hr] using
        (ExecStep.control (ControlReduces.labelDone (types := types)
          (n := n) (continuation := continuation) (vs := p.stack)))⟩
  | instr (.br 0) :: tail =>
    match operands p.stack n with
    | none => exact none
    | some args =>
      exact some ⟨values args.args ++ instructions continuation, by
        simpa [p.reconstruct, hr, args.reconstruct, values, List.map_append,
          List.append_assoc] using
          (ExecStep.control (ControlReduces.brZero (types := types)
            (discarded := args.below) (results := args.args)
            (continuation := continuation) (tail := tail) args.arity))⟩
  | instr (.br (l + 1)) :: tail =>
    exact some ⟨values p.stack ++ [instr (.br l)], by
      simpa [p.reconstruct, hr, List.append_assoc] using
        (ExecStep.control (ControlReduces.brSucc (types := types) (n := n)
          (continuation := continuation) (vs := p.stack) (l := l) (tail := tail)))⟩
  | instr .return_ :: tail =>
    exact some ⟨values p.stack ++ [instr .return_], by
      simpa [p.reconstruct, hr, List.append_assoc] using
        (ExecStep.control (ControlReduces.returnLabel (types := types)
          (n := n) (continuation := continuation) (vs := p.stack) (tail := tail)))⟩
  | _ =>
    match hb : body with
    | [.trap] => exact some ⟨[.trap], .control .labelTrap⟩
    | _ => exact inner.map fun next =>
        ⟨[.label n continuation next.val], .label (by simpa [hb] using next.property)⟩

private def pureFrameStep (types : TypeContext) (n : Nat) (state : Frame)
    (body : List AdminInstr) (inner : CheckedStep state.module.types body) :
    CheckedStep types [.frame n state body] := by
  let p := splitValues body
  match hr : p.rest with
  | [] =>
    if h : p.stack.length = n then
      exact some ⟨values p.stack, by
        simpa [p.reconstruct, hr] using
          (ExecStep.activation (types := types) (FrameReduces.done (state := state) h))⟩
    else exact none
  | instr .return_ :: tail =>
    match operands p.stack n with
    | none => exact none
    | some args =>
      exact some ⟨values args.args, by
        simpa [p.reconstruct, hr, args.reconstruct, values, List.map_append,
          List.append_assoc] using
          (ExecStep.activation (types := types) (FrameReduces.return_
            (state := state) (discarded := args.below) (results := args.args)
            (tail := tail) args.arity))⟩
  | _ =>
    match hb : body with
    | [.trap] => exact some ⟨[.trap], .activation .trap⟩
    | _ => exact inner.map fun next =>
        ⟨[.frame n state next.val], .frame (by simpa [hb] using next.property)⟩

private def frameStep (types : TypeContext) (n : Nat) (state : Frame)
    (body : List AdminInstr) (inner : CheckedStep state.module.types body) :
    CheckedStep types [.frame n state body] :=
  match checkedLocalStep state body with
  | some next => some ⟨[.frame n next.val.1 next.val.2], .localFrame next.property⟩
  | none => pureFrameStep types n state body inner

private def scan (types : TypeContext) (es : List AdminInstr) (stack : List Value) :
    CheckedStep types (values stack ++ es) := by
  match es with
  | [] => exact none
  | instr (.const v) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using scan types tail (stack ++ [v])
  | instr i :: tail =>
    simpa [values] using inContext [] tail (focusStep types stack i)
  | .trap :: tail =>
    if h : stack.length + tail.length = 0 then exact none
    else
      exact some ⟨[.trap], by
        simpa [List.append_assoc] using
          (ExecStep.trap (types := types) (vs := stack) (tail := tail) (by
            intro he
            have hl := congrArg List.length he
            simp [values] at hl
            omega))⟩
  | .label n continuation body :: tail =>
    simpa using inContext stack tail (labelStep types n continuation body (scan types body []))
  | .frame n state body :: tail =>
    simpa using inContext stack tail
      (frameStep types n state body (scan state.module.types body []))
  | .invoke _ _ :: _ | .castFunc _ :: _ | .invokeRef _ :: _
  | .castDefined _ :: _ | .invokeDefined _ :: _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

private def checkedStep (types : TypeContext) (es : List AdminInstr) : CheckedStep types es :=
  scan types es []

/-- One semantic step, including nested labels. `none` means this strategy cannot step. -/
def step (types : TypeContext) (es : List AdminInstr) : Option (List AdminInstr) :=
  (checkedStep types es).map Subtype.val

theorem step_sound (h : step types es = some next) : ExecStep types es next := by
  unfold step at h
  cases hs : checkedStep types es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

inductive StepOutcome where
  | next (code : List AdminInstr)
  | finished (results : List Value)
  | trapped
  | stuck
  deriving BEq, Repr

/-- Classify terminal states separately from malformed or unbound instructions. -/
def stepOutcome (types : TypeContext) (es : List AdminInstr) : StepOutcome :=
  match step types es with
  | some next => .next next
  | none =>
    let p := splitValues es
    match p.rest with
    | [] => .finished p.stack
    | _ => match es with
      | [.trap] => .trapped
      | _ => .stuck

theorem stepOutcome_finished (h : stepOutcome types es = .finished vs) : es = values vs := by
  cases hs : step types es with
  | some next => simp [stepOutcome, hs] at h
  | none =>
    cases hr : (splitValues es).rest with
    | nil =>
      have hv : (splitValues es).stack = vs := by simpa [stepOutcome, hs, hr] using h
      simpa [hr, hv] using (splitValues es).reconstruct
    | cons x xs =>
      simp only [stepOutcome, hs, hr] at h
      split at h <;> cases h

theorem stepOutcome_trapped (h : stepOutcome types es = .trapped) : es = [.trap] := by
  cases hs : step types es with
  | some next => simp [stepOutcome, hs] at h
  | none =>
    cases hr : (splitValues es).rest with
    | nil => simp [stepOutcome, hs, hr] at h
    | cons x xs =>
      simp only [stepOutcome, hs, hr] at h
      split at h
      · rfl
      · cases h

private def checkedRun (types : TypeContext) : (fuel : Nat) → (es : List AdminInstr) →
    { final : List AdminInstr // ExecSteps types es final }
  | 0, es => ⟨es, .refl⟩
  | fuel + 1, es =>
    match checkedStep types es with
    | none => ⟨es, .refl⟩
    | some next =>
      let result := checkedRun types fuel next.val
      ⟨result.val, .cons next.property result.property⟩

inductive RunStatus where
  | finished (results : List Value)
  | trapped
  | stuck
  | exhausted
  deriving BEq, Repr

structure RunResult where
  state : List AdminInstr
  status : RunStatus
  deriving BEq, Repr

/-- Execute at most `fuel` semantic steps; exhausted execution preserves its residual state. -/
def run (fuel : Nat) (types : TypeContext) (es : List AdminInstr) : RunResult :=
  let result := checkedRun types fuel es
  let status := match stepOutcome types result.val with
    | .finished vs => RunStatus.finished vs
    | .trapped => .trapped
    | .stuck => .stuck
    | .next _ => .exhausted
  ⟨result.val, status⟩

theorem run_sound : ExecSteps types es (run fuel types es).state :=
  (checkedRun types fuel es).property

theorem run_finished (h : (run fuel types es).status = .finished vs) :
    (run fuel types es).state = values vs := by
  unfold run at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hs
    cases h
    exact stepOutcome_finished hs
  · cases h
  · cases h
  · cases h

theorem run_trapped (h : (run fuel types es).status = .trapped) :
    (run fuel types es).state = [.trap] := by
  unfold run at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i hs
    exact stepOutcome_trapped hs
  · cases h
  · cases h

end Wasm
