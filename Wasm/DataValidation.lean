import Wasm.CallValidation

namespace Wasm

/-- Constant instructions in the represented integer/nullable-reference fragment. -/
inductive ConstantInstr (globals : List GlobalType) : Instr → Prop where
  | const (ht : v.type.IsNumber := by trivial) : ConstantInstr globals (.const v)
  | binop (ht : type.IsInteger := by trivial) : ConstantInstr globals (.binop type op)
  | refNull : ConstantInstr globals (.refNull kind)
  | refFunc : ConstantInstr globals (.refFunc x)
  | global (h : globals[x]? = some ⟨.const, type⟩) : ConstantInstr globals (.globalGet x)

inductive DataTyping (context : FunctionContext) : Data → Prop where
  | passive : DataTyping context ⟨bytes, .passive⟩
  | active (hm : context.mems[x]? = some memory)
      (ht : RuntimeSeqTyping context [] offset [] [memory.addrType])
      (hc : ∀ i ∈ offset, ConstantInstr context.globals i) :
      DataTyping context ⟨bytes, .active x offset⟩

end Wasm
