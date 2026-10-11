import Wasm.Runtime

namespace Wasm

/-- Packed fields retain their low bits; ordinary fields retain their value. -/
def Types.StorageType.packValue : Types.StorageType → Value → Option Value
  | .val _, value => some value
  | .i8, .i32 bits => some (.i32 ((bits.truncate 8).zeroExtend 32))
  | .i16, .i32 bits => some (.i32 ((bits.truncate 16).zeroExtend 32))
  | _, _ => none

/-- Packed reads require a signedness immediate; ordinary reads have none. -/
def Types.StorageType.unpackValue : Types.StorageType → Option Bool → Value → Option Value
  | .val _, none, value => some value
  | .i8, some true, .i32 bits => some (.i32 ((bits.truncate 8).signExtend 32))
  | .i8, some false, .i32 bits => some (.i32 ((bits.truncate 8).zeroExtend 32))
  | .i16, some true, .i32 bits => some (.i32 ((bits.truncate 16).signExtend 32))
  | .i16, some false, .i32 bits => some (.i32 ((bits.truncate 16).zeroExtend 32))
  | _, _, _ => none

def Types.StorageType.byteWidth? : Types.StorageType → Option Nat
  | .i8 => some 1
  | .i16 => some 2
  | .val .i32 | .val .f32 => some 4
  | .val .i64 | .val .f64 => some 8
  | .val .v128 => some 16
  | _ => none

def Store.struct? (store : Store) (address : StructAddr) : Option StructInst :=
  store.structs[address.index]?

def Store.array? (store : Store) (address : ArrayAddr) : Option ArrayInst :=
  store.arrays[address.index]?

def Store.allocateStruct (store : Store) (object : StructInst) : StructAddr × Store :=
  (⟨store.structs.length⟩, {store with structs := store.structs ++ [object]})

def Store.allocateArray (store : Store) (object : ArrayInst) : ArrayAddr × Store :=
  (⟨store.arrays.length⟩, {store with arrays := store.arrays ++ [object]})

theorem Store.allocateStruct_lookup (store : Store) (object : StructInst) :
    (store.allocateStruct object).2.struct? (store.allocateStruct object).1 = some object := by
  simp [Store.allocateStruct, Store.struct?]

theorem Store.allocateArray_lookup (store : Store) (object : ArrayInst) :
    (store.allocateArray object).2.array? (store.allocateArray object).1 = some object := by
  simp [Store.allocateArray, Store.array?]

theorem Store.allocateStruct_preserves (store : Store) (object : StructInst)
    (address : StructAddr) (h : address.index < store.structs.length) :
    (store.allocateStruct object).2.struct? address = store.struct? address := by
  simp [Store.allocateStruct, Store.struct?, List.getElem?_append, h]

theorem Store.allocateArray_preserves (store : Store) (object : ArrayInst)
    (address : ArrayAddr) (h : address.index < store.arrays.length) :
    (store.allocateArray object).2.array? address = store.array? address := by
  simp [Store.allocateArray, Store.array?, List.getElem?_append, h]

end Wasm
