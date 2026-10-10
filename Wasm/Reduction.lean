import Wasm.Numerics

/-!
Small-step reduction of the integer/parametric fragment. Lists have the specification's
order: the rightmost value is the top of the operand stack. Store and frame components
are omitted here because every implemented rule leaves them unchanged.
Source: https://webassembly.github.io/spec/core/exec/instructions.html
-/

namespace Wasm

open AdminInstr Instr

/-- Local redex rules, before closure under evaluation contexts. -/
inductive Reduces : List AdminInstr → List AdminInstr → Prop where
  | nop : Reduces [instr .nop] []
  | unreachable : Reduces [instr .unreachable] [.trap]
  | drop : Reduces [instr (.const v), instr .drop] []
  | selectZero : Reduces
      [instr (.const a), instr (.const b), instr (.const (.i32 0)), instr (.select ts)]
      [instr (.const b)]
  | selectNonzero (h : c ≠ 0) : Reduces
      [instr (.const a), instr (.const b), instr (.const (.i32 c)), instr (.select ts)]
      [instr (.const a)]
  | binop (h : evalBinOp t op a b = some result) : Reduces
      [instr (.const a), instr (.const b), instr (.binop t op)] [instr (.const result)]
  | eqz (h : evalEqz t a = some result) : Reduces
      [instr (.const a), instr (.eqz t)] [instr (.const result)]

/-- Executable local reduction. `none` means no rule applies, rather than a Wasm trap. -/
def reduce : List AdminInstr → Option (List AdminInstr)
  | [instr .nop] => some []
  | [instr .unreachable] => some [.trap]
  | [instr (.const _), instr .drop] => some []
  | [instr (.const a), instr (.const b), instr (.const (.i32 c)), instr (.select _)] =>
      some [instr (.const (if c = 0 then b else a))]
  | [instr (.const a), instr (.const b), instr (.binop t op)] =>
      (evalBinOp t op a b).map (fun v => [instr (.const v)])
  | [instr (.const a), instr (.eqz t)] =>
      (evalEqz t a).map (fun v => [instr (.const v)])
  | _ => none

theorem reduce_complete (h : Reduces es es') : reduce es = some es' := by
  cases h <;> simp_all [reduce]

theorem reduce_sound (h : reduce es = some es') : Reduces es es' := by
  unfold reduce at h
  split at h
  · cases h; exact .nop
  · cases h; exact .unreachable
  · cases h; exact .drop
  · split at h
    · cases h; rename_i a b c ts hc; subst c; exact .selectZero
    · cases h; exact .selectNonzero (by assumption)
  · rename_i a b t op
    cases he : evalBinOp t op a b with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .binop he
  · rename_i a t
    cases he : evalEqz t a with
    | none => simp [he] at h
    | some v => simp [he] at h; subst es'; exact .eqz he
  · cases h

theorem reduce_iff : reduce es = some es' ↔ Reduces es es' :=
  ⟨reduce_sound, reduce_complete⟩

theorem reduces_deterministic (h₁ : Reduces es a) (h₂ : Reduces es b) : a = b := by
  have h := (reduce_complete h₁).symm.trans (reduce_complete h₂)
  exact Option.some.inj h

/-- Flat evaluation contexts: a value prefix and an arbitrary instruction suffix. -/
inductive Step : List AdminInstr → List AdminInstr → Prop where
  | context (h : Reduces redex result) :
      Step (values vs ++ redex ++ tail) (values vs ++ result ++ tail)
  | trap (h : values vs ++ [.trap] ++ tail ≠ [.trap]) :
      Step (values vs ++ [.trap] ++ tail) [.trap]

/-- Reflexive transitive closure; no execution fuel is part of the semantics. -/
inductive Steps : List AdminInstr → List AdminInstr → Prop where
  | refl : Steps es es
  | cons : Step es middle → Steps middle result → Steps es result

end Wasm
