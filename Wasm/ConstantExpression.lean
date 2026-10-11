import Wasm.Module
import Wasm.Configuration

namespace Wasm

/-- Constant expression evaluation, with the top value at the head of the auxiliary stack. -/
inductive ConstEval (store : Store) (module : ModuleInst) :
    List Instr → List Value → List Value → Prop where
  | i31 (hr : ConstEval store module rest (.ref (.i31 (bits.truncate 31)) :: stack) result) :
      ConstEval store module (.gcReference .i31New :: rest) (.i32 bits :: stack) result
  | anyConvertExtern (hr : ConstEval store module rest
      (.ref reference.internalize :: stack) result) :
      ConstEval store module (.gcReference .anyConvertExtern :: rest) (.ref reference :: stack)
        result
  | externConvertAny (hr : ConstEval store module rest
      (.ref reference.externalize :: stack) result) :
      ConstEval store module (.gcReference .externConvertAny :: rest) (.ref reference :: stack)
        result
  | empty : ConstEval store module [] stack stack
  | const : ConstEval store module rest (v :: stack) result →
      ConstEval store module (.const v :: rest) stack result
  | refNull (ht : kind.close? module.definedTypes = some closed) :
      ConstEval store module rest (.ref (.null closed) :: stack) result →
      ConstEval store module (.refNull kind :: rest) stack result
  | refFunc (ha : module.funcAddr? x = some address)
      (hr : ConstEval store module rest (.ref (.func address) :: stack) result) :
      ConstEval store module (.refFunc x :: rest) stack result
  | global (hg : store.resolveGlobal? module x = some global)
      (hm : global.type.mutability = .const)
      (hr : ConstEval store module rest (global.value :: stack) result) :
      ConstEval store module (.globalGet x :: rest) stack result
  | binop (he : evalBinOp type op a b = some v)
      (hr : ConstEval store module rest (v :: stack) result) :
      ConstEval store module (.binop type op :: rest) (b :: a :: stack) result

private def checkedConstEval (store : Store) (module : ModuleInst) :
    (code : List Instr) → (stack : List Value) →
      Option { result : List Value // ConstEval store module code stack result }
  | .gcReference .i31New :: rest, .i32 bits :: stack =>
    (checkedConstEval store module rest (.ref (.i31 (bits.truncate 31)) :: stack)).map
      fun result => ⟨result.val, .i31 result.property⟩
  | .gcReference .anyConvertExtern :: rest, .ref reference :: stack =>
    (checkedConstEval store module rest (.ref reference.internalize :: stack)).map
      fun result => ⟨result.val, .anyConvertExtern result.property⟩
  | .gcReference .externConvertAny :: rest, .ref reference :: stack =>
    (checkedConstEval store module rest (.ref reference.externalize :: stack)).map
      fun result => ⟨result.val, .externConvertAny result.property⟩
  | [], stack => some ⟨stack, .empty⟩
  | .const v :: rest, stack =>
    (checkedConstEval store module rest (v :: stack)).map fun result =>
      ⟨result.val, .const result.property⟩
  | .refNull kind :: rest, stack => by
    match ht : kind.close? module.definedTypes with
    | none => exact none
    | some closed =>
      exact (checkedConstEval store module rest (.ref (.null closed) :: stack)).map fun result =>
        ⟨result.val, .refNull ht result.property⟩
  | .refFunc x :: rest, stack => by
    match ha : module.funcAddr? x with
    | none => exact none
    | some address =>
      exact (checkedConstEval store module rest (.ref (.func address) :: stack)).map
        fun result => ⟨result.val, .refFunc ha result.property⟩
  | .globalGet x :: rest, stack => by
    match hg : store.resolveGlobal? module x with
    | none => exact none
    | some global =>
      if hm : global.type.mutability = .const then
        exact (checkedConstEval store module rest (global.value :: stack)).map fun result =>
          ⟨result.val, .global hg hm result.property⟩
      else exact none
  | .binop type op :: rest, b :: a :: stack => by
    match he : evalBinOp type op a b with
    | none => exact none
    | some v => exact (checkedConstEval store module rest (v :: stack)).map fun result =>
        ⟨result.val, .binop he result.property⟩
  | _ :: _, _ => none

def evalConst (store : Store) (module : ModuleInst) (code : List Instr) :
    Option { value : Value // ConstEval store module code [] [value] } := by
  match checkedConstEval store module code [] with
  | none => exact none
  | some result =>
    match he : result.val with
    | [value] => exact some ⟨value, he ▸ result.property⟩
    | _ => exact none

/-- Constant evaluation agrees with ordinary configuration reduction. Constants themselves
are already values; only global reads and arithmetic require reduction steps.
-/
theorem ConstEval.toConfigSteps (h : ConstEval store module code stack result) :
    ConfigSteps ⟨store, { module }, values stack.reverse ++ instructions code⟩
      ⟨store, { module }, values result.reverse⟩ := by
  induction h with
  | @i31 rest stack result bits _ ih =>
    have hs := ConfigStep.references (store := store) (frame := { module })
      (ReferenceStep.context (vs := stack.reverse) (tail := instructions rest)
        (.redex (.gc (op := .i31New) (args := [.i32 bits]) rfl)))
    apply ConfigSteps.cons (by
      simpa [values, instructions, List.reverse_cons, List.map_append, List.append_assoc] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @anyConvertExtern rest stack result reference _ ih =>
    have hs := ConfigStep.references (store := store) (frame := { module })
      (ReferenceStep.context (vs := stack.reverse) (tail := instructions rest)
        (.redex (.gc (op := .anyConvertExtern) (args := [.ref reference]) rfl)))
    apply ConfigSteps.cons (by
      simpa [values, instructions, List.reverse_cons, List.map_append, List.append_assoc] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @externConvertAny rest stack result reference _ ih =>
    have hs := ConfigStep.references (store := store) (frame := { module })
      (ReferenceStep.context (vs := stack.reverse) (tail := instructions rest)
        (.redex (.gc (op := .externConvertAny) (args := [.ref reference]) rfl)))
    apply ConfigSteps.cons (by
      simpa [values, instructions, List.reverse_cons, List.map_append, List.append_assoc] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | empty => simp only [instructions, List.map_nil, List.append_nil]; exact .refl
  | const _ ih =>
    simpa [values, instructions, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @refNull closed rest stack result kind ht _ ih =>
    have hs := ConfigStep.references (store := store) (frame := { module })
      (ReferenceStep.context (vs := stack.reverse) (tail := instructions rest)
        (.redex (.null ht)))
    apply ConfigSteps.cons (by simpa [instructions] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @refFunc x address rest stack result ha _ ih =>
    have hs := ConfigStep.references (store := store) (frame := { module })
      (ReferenceStep.context (vs := stack.reverse) (tail := instructions rest) (.redex (.func ha)))
    apply ConfigSteps.cons (by simpa [instructions] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @global x global rest stack result hg _ _ ih =>
    unfold Store.resolveGlobal? at hg
    cases ha : module.globalAddr? x with
    | none => simp [ha] at hg
    | some address =>
      simp [ha] at hg
      have hs := ConfigStep.globals
        (GlobalStep.context (vs := stack.reverse) (tail := instructions rest)
          (.get (state := { module }) ha hg))
      apply ConfigSteps.cons (by simpa [instructions] using hs)
      simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih
  | @binop type op a b v rest stack result he _ ih =>
    have hs := ConfigStep.pure (store := store) (frame := { module })
      (ExecStep.context (vs := stack.reverse) (tail := instructions rest) (.primitive (.binop he)))
    apply ConfigSteps.cons (by
      simpa [values, instructions, List.reverse_cons, List.map_append, List.append_assoc] using hs)
    simpa [values, List.reverse_cons, List.map_append, List.append_assoc] using ih

theorem ConfigSteps.module_preserved (h : ConfigSteps config next) :
    next.frame.module = config.frame.module := by
  induction h with
  | refl => rfl
  | cons step _ ih => exact ih.trans step.module_preserved

/-- Allocating constants thread the store and carry ordinary configuration reductions. -/
inductive ConstAllocated (store : Store) (module : ModuleInst) (code : List Instr) :
    Store → Value → Prop where
  | evaluated (steps : ConfigSteps ⟨store, {module}, instructions code⟩
        ⟨next, frame, values [value]⟩) (owner : frame.module = module) :
      ConstAllocated store module code next value

def evalAllocatedConst (store : Store) (module : ModuleInst) (code : List Instr) :
    Option {result : Store × Value // ConstAllocated store module code result.1 result.2} := by
  let initial : Configuration := ⟨store, {module}, instructions code⟩
  let result := runConfiguration ((code.length + 1) * 4) initial
  match hs : result.status with
  | .finished vs =>
    match hv : vs with
    | [value] =>
      have finished : result.status = .finished [value] := by simpa [hv] using hs
      have code_eq : result.state.code = values [value] := runConfiguration_finished finished
      have steps : ConfigSteps initial result.state := runConfiguration_sound
      exact some ⟨(result.state.store, value), .evaluated
        (by rw [← code_eq]; exact steps) steps.module_preserved⟩
    | _ => exact none
  | _ => exact none

end Wasm
