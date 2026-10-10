import Wasm.BulkMemory

namespace Wasm

inductive BulkInstrTyping (mems : List MemoryType) (dataCount : Nat) :
    Instr → List ValType → List ValType → Prop where
  | fill (hm : mems[x]? = some memory) :
      BulkInstrTyping mems dataCount (.memoryFill x) [memory.addrType, .i32, memory.addrType] []
  | copy (hd : mems[x]? = some dst) (hs : mems[y]? = some src) :
      BulkInstrTyping mems dataCount (.memoryCopy x y)
        [dst.addrType, src.addrType, dst.addrType.minAddress src.addrType] []
  | init (hm : mems[x]? = some memory) (hd : y < dataCount) :
      BulkInstrTyping mems dataCount (.memoryInit x y) [memory.addrType, .i32, .i32] []
  | drop (hd : y < dataCount) : BulkInstrTyping mems dataCount (.dataDrop y) [] []
  | weaken : BulkInstrTyping mems dataCount i input output →
      BulkInstrTyping mems dataCount i (ts₀ ++ input) (ts₀ ++ output)

end Wasm
