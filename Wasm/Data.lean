import Wasm.Memory

namespace Wasm

inductive DataMode where
  | passive
  | active (memory : Nat) (offset : List Instr)
  deriving BEq, Repr

structure Data where
  bytes : Array Byte
  mode : DataMode
  deriving BEq, Repr

def ModuleInst.dataAddr? (module : ModuleInst) (index : Nat) : Option DataAddr :=
  module.datas[index]?

def Store.data? (store : Store) (address : DataAddr) : Option DataInst :=
  store.datas[address.index]?

def Store.resolveData? (store : Store) (module : ModuleInst) (index : Nat) : Option DataInst :=
  (module.dataAddr? index).bind store.data?

def Store.allocateData (store : Store) (data : DataInst) : DataAddr × Store :=
  (⟨store.datas.length⟩, { store with datas := store.datas ++ [data] })

theorem Store.allocateData_lookup (store : Store) (data : DataInst) :
    (store.allocateData data).2.data? (store.allocateData data).1 = some data := by
  simp [Store.allocateData, Store.data?]

theorem Store.allocateData_preserves (store : Store) (data : DataInst) (address : DataAddr)
    (h : address.index < store.datas.length) :
    (store.allocateData data).2.data? address = store.data? address := by
  simp [Store.allocateData, Store.data?, List.getElem?_append, h]

def Store.dropData (store : Store) (address : DataAddr) : Store :=
  { store with datas := store.datas.set address.index ⟨#[]⟩ }

theorem Store.dropData_lookup (store : Store) (address : DataAddr)
    (h : address.index < store.datas.length) :
    (store.dropData address).data? address = some ⟨#[]⟩ := by
  simp [Store.dropData, Store.data?, h]

/-- Initialization code for an already allocated segment. Offset validation and full module
instantiation are separate; the caller must supply a validated constant expression.
-/
def Data.initializer (data : Data) (index : Nat) : List Instr :=
  match data.mode with
  | .passive => []
  | .active memory offset => offset ++
      [.const (.i32 0), .const (Value.ofNat .i32 data.bytes.size),
        .memoryInit memory index, .dataDrop index]

end Wasm
