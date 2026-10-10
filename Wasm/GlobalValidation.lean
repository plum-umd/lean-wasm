import Wasm.Syntax

namespace Wasm

/-! Global typing enforces mutability statically.
https://webassembly.github.io/spec/core/valid/instructions.html#variable-instructions
-/
inductive GlobalInstrTyping (globals : List GlobalType) :
    Instr → List ValType → List ValType → Prop where
  | get (h : globals[x]? = some gt) : GlobalInstrTyping globals (.globalGet x) [] [gt.valType]
  | set (h : globals[x]? = some ⟨.var, t⟩) : GlobalInstrTyping globals (.globalSet x) [t] []
  | weaken : GlobalInstrTyping globals i input output →
      GlobalInstrTyping globals i (ts₀ ++ input) (ts₀ ++ output)

theorem GlobalInstrTyping.set_mutable
    (h : GlobalInstrTyping globals (.globalSet x) input output) :
    ∃ t, globals[x]? = some ⟨.var, t⟩ := by
  generalize hi : Instr.globalSet x = i at h
  induction h with
  | get _ => cases hi
  | set h => cases hi; exact ⟨_, h⟩
  | weaken _ ih => exact ih hi

theorem GlobalInstrTyping.immutable_set_rejected
    (hg : globals[x]? = some ⟨.const, t⟩) :
    ¬ GlobalInstrTyping globals (.globalSet x) input output := by
  intro h
  obtain ⟨_, hm⟩ := h.set_mutable
  simp [hg] at hm

end Wasm
