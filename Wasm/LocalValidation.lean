import Wasm.ControlValidation

namespace Wasm

/-! Stack typing with an explicit context of local value types. `FuncTyping` also requires
the initialization check in `LocalInitialization`; stack typing alone does not certify reads.
https://webassembly.github.io/spec/core/valid/instructions.html#variable-instructions
-/
mutual
  inductive FunctionInstrTyping (types : TypeContext) (locals : List ValType) :
      LabelContext → Instr → List ValType → List ValType → Prop where
    | plain : ControlInstrTyping types labels i input output →
        FunctionInstrTyping types locals labels i input output
    | localGet (h : locals[x]? = some t) :
        FunctionInstrTyping types locals labels (.localGet x) [] [t]
    | localSet (h : locals[x]? = some t) :
        FunctionInstrTyping types locals labels (.localSet x) [t] []
    | localTee (h : locals[x]? = some t) :
        FunctionInstrTyping types locals labels (.localTee x) [t] [t]
    | block (ht : bt.resolve types = some ft)
        (hb : FunctionSeqTyping types locals (ft.results :: labels) body ft.params ft.results) :
        FunctionInstrTyping types locals labels (.block bt body) ft.params ft.results
    | loop (ht : bt.resolve types = some ft)
        (hb : FunctionSeqTyping types locals (ft.params :: labels) body ft.params ft.results) :
        FunctionInstrTyping types locals labels (.loop bt body) ft.params ft.results
    | if_ (ht : bt.resolve types = some ft)
        (hy : FunctionSeqTyping types locals (ft.results :: labels) yes ft.params ft.results)
        (hn : FunctionSeqTyping types locals (ft.results :: labels) no ft.params ft.results) :
        FunctionInstrTyping types locals labels (.if_ bt yes no) (ft.params ++ [.i32]) ft.results
    | weaken : FunctionInstrTyping types locals labels i input output →
        FunctionInstrTyping types locals labels i (ts₀ ++ input) (ts₀ ++ output)

  inductive FunctionSeqTyping (types : TypeContext) (locals : List ValType) :
      LabelContext → List Instr → List ValType → List ValType → Prop where
    | empty : FunctionSeqTyping types locals labels [] ts ts
    | cons : FunctionInstrTyping types locals labels i input middle →
        FunctionSeqTyping types locals labels rest middle output →
        FunctionSeqTyping types locals labels (i :: rest) input output
    | weaken : FunctionSeqTyping types locals labels code input output →
        FunctionSeqTyping types locals labels code (ts₀ ++ input) (ts₀ ++ output)
end

end Wasm
