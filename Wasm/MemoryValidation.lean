import Wasm.Memory

namespace Wasm

def MemArg.Valid (arg : MemArg) (addrType : ValType) (bytes : Nat) : Prop :=
  2 ^ arg.align ≤ bytes ∧ arg.offset < 2 ^ addrType.bits

instance (arg : MemArg) (addrType : ValType) (bytes : Nat) :
    Decidable (arg.Valid addrType bytes) := by
  unfold MemArg.Valid
  infer_instance

inductive MemoryInstrTyping (mems : List MemoryType) :
    Instr → List ValType → List ValType → Prop where
  | load (hm : mems[x]? = some memoryType) (ha : arg.Valid memoryType.addrType op.bytes) :
      MemoryInstrTyping mems (.load op x arg) [memoryType.addrType] [op.type]
  | store (hm : mems[x]? = some memoryType) (ha : arg.Valid memoryType.addrType op.bytes) :
      MemoryInstrTyping mems (.store op x arg) [memoryType.addrType, op.type] []
  | size (hm : mems[x]? = some memoryType) :
      MemoryInstrTyping mems (.memorySize x) [] [memoryType.addrType]
  | grow (hm : mems[x]? = some memoryType) :
      MemoryInstrTyping mems (.memoryGrow x) [memoryType.addrType] [memoryType.addrType]
  | weaken : MemoryInstrTyping mems i input output →
      MemoryInstrTyping mems i (ts₀ ++ input) (ts₀ ++ output)

end Wasm
