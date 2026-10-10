import Wasm.Validation

/-!
Structured-control validation in an explicit label context (innermost label first).
https://webassembly.github.io/spec/core/valid/instructions.html#control-instructions
Block signatures are restricted to the fragment's function types with no local effects.
-/

namespace Wasm

abbrev LabelContext := List (List ValType)

mutual
  inductive ControlInstrTyping (types : TypeContext) :
      LabelContext → Instr → List ValType → List ValType → Prop where
    | plain : InstrTyping i input output → ControlInstrTyping types labels i input output
    | block (ht : bt.resolve types = some ft)
        (hb : ControlSeqTyping types (ft.results :: labels) body ft.params ft.results) :
        ControlInstrTyping types labels (.block bt body) ft.params ft.results
    | loop (ht : bt.resolve types = some ft)
        (hb : ControlSeqTyping types (ft.params :: labels) body ft.params ft.results) :
        ControlInstrTyping types labels (.loop bt body) ft.params ft.results
    | if_ (ht : bt.resolve types = some ft)
        (hy : ControlSeqTyping types (ft.results :: labels) yes ft.params ft.results)
        (hn : ControlSeqTyping types (ft.results :: labels) no ft.params ft.results) :
        ControlInstrTyping types labels (.if_ bt yes no) (ft.params ++ [.i32]) ft.results
    | br (ht : labels[l]? = some ts) :
        ControlInstrTyping types labels (.br l) (input ++ ts) output
    | brIf (ht : labels[l]? = some ts) :
        ControlInstrTyping types labels (.brIf l) (ts ++ [.i32]) ts
    | brTable (hd : labels[fallback]? = some ts)
        (ht : ∀ l ∈ targets, labels[l]? = some ts) :
        ControlInstrTyping types labels (.brTable targets fallback)
          (input ++ ts ++ [.i32]) output
    | weaken : ControlInstrTyping types labels i input output →
        ControlInstrTyping types labels i (ts₀ ++ input) (ts₀ ++ output)

  inductive ControlSeqTyping (types : TypeContext) :
      LabelContext → List Instr → List ValType → List ValType → Prop where
    | empty : ControlSeqTyping types labels [] ts ts
    | cons : ControlInstrTyping types labels i input middle →
        ControlSeqTyping types labels rest middle output →
        ControlSeqTyping types labels (i :: rest) input output
    | weaken : ControlSeqTyping types labels code input output →
        ControlSeqTyping types labels code (ts₀ ++ input) (ts₀ ++ output)
end

theorem SeqTyping.toControlSeqTyping (h : SeqTyping code input output) :
    ControlSeqTyping types labels code input output := by
  induction h with
  | empty => exact .empty
  | cons h _ ih => exact .cons (.plain h) ih
  | weaken _ ih => exact .weaken ih

end Wasm
