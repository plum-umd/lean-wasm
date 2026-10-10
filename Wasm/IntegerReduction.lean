import Wasm.Integers

namespace Wasm

open AdminInstr Instr

/-- Numeric instruction rules, including the specification's undefined-operation trap. -/
inductive IntegerReduces : List AdminInstr → List AdminInstr → Prop where
  | unary (h : evalUnary t op a = some v) :
      IntegerReduces [instr (.const a), instr (.intUnary t op)] (values [v])
  | binary (h : evalBinary t op a b = some result) :
      IntegerReduces [instr (.const a), instr (.const b), instr (.intBinary t op)] result.code
  | rel (h : evalRel t op a b = some v) :
      IntegerReduces [instr (.const a), instr (.const b), instr (.intRel t op)] (values [v])
  | conversion (h : evalConversion op a = some v) :
      IntegerReduces [instr (.const a), instr (.intConvert op)] (values [v])

def reduceInteger : List AdminInstr → Option (List AdminInstr)
  | [instr (.const a), instr (.intUnary t op)] => (evalUnary t op a).map (fun v => values [v])
  | [instr (.const a), instr (.const b), instr (.intBinary t op)] =>
      (evalBinary t op a b).map NumericResult.code
  | [instr (.const a), instr (.const b), instr (.intRel t op)] =>
      (evalRel t op a b).map (fun v => values [v])
  | [instr (.const a), instr (.intConvert op)] =>
      (evalConversion op a).map (fun v => values [v])
  | _ => none

theorem reduceInteger_complete (h : IntegerReduces es es') : reduceInteger es = some es' := by
  cases h <;> simp_all [reduceInteger]

theorem reduceInteger_sound (h : reduceInteger es = some es') : IntegerReduces es es' := by
  unfold reduceInteger at h
  split at h
  · rename_i a t op
    cases he : evalUnary t op a with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .unary he
  · rename_i a b t op
    cases he : evalBinary t op a b with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .binary he
  · rename_i a b t op
    cases he : evalRel t op a b with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .rel he
  · rename_i a op
    cases he : evalConversion op a with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .conversion he
  · cases h

theorem reduceInteger_iff : reduceInteger es = some es' ↔ IntegerReduces es es' :=
  ⟨reduceInteger_sound, reduceInteger_complete⟩

theorem integerReduces_deterministic (h₁ : IntegerReduces es a) (h₂ : IntegerReduces es b) :
    a = b :=
  Option.some.inj ((reduceInteger_complete h₁).symm.trans (reduceInteger_complete h₂))

end Wasm
