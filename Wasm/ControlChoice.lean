import Wasm.Control

namespace Wasm

open AdminInstr Instr

/-- Executable lowering of conditionals and branch selection, on an exact local redex. -/
def reduceControlChoice : List AdminInstr → Option (List AdminInstr)
  | [instr (.const (.i32 c)), instr (.if_ bt yes no)] =>
      some [instr (.block bt (if c = 0 then no else yes))]
  | [instr (.const (.i32 c)), instr (.brIf l)] =>
      some (if c = 0 then [] else [instr (.br l)])
  | [instr (.const (.i32 c)), instr (.brTable targets fallback)] =>
      some [instr (.br (targets[c.toNat]?.getD fallback))]
  | _ => none

theorem reduceControlChoice_sound (h : reduceControlChoice es = some es') :
    ControlReduces types es es' := by
  unfold reduceControlChoice at h
  split at h
  · split at h
    · cases h; rename_i c bt yes no hc; subst c; exact .ifZero
    · cases h; exact .ifNonzero (by assumption)
  · split at h
    · cases h; rename_i c l hc; subst c; exact .brIfZero
    · cases h; exact .brIfNonzero (by assumption)
  · rename_i c targets fallback
    cases ht : targets[c.toNat]? with
    | none =>
      simp only [ht, Option.getD_none, Option.some.injEq] at h
      subst es'
      exact .brTableDefault (List.getElem?_eq_none_iff.mp ht)
    | some l =>
      simp only [ht, Option.getD_some, Option.some.injEq] at h
      subst es'
      exact .brTableHit ht
  · cases h

theorem reduceControlChoice_step (h : reduceControlChoice es = some es') :
    ExecStep types es es' := .control (reduceControlChoice_sound h)

end Wasm
