import Wasm.Data

namespace Wasm

def ValType.minAddress : ValType → ValType → ValType
  | .i64, .i64 => .i64
  | _, _ => .i32

def fillCode (type : ValType) (x i : Nat) (v : Value) (n : Nat) : List AdminInstr :=
  instructions [.const (Value.ofNat type i), .const v, .store .i32_8 x {},
    .const (Value.ofNat type (i + 1)), .const v, .const (Value.ofNat type (n - 1)),
    .memoryFill x]

def copyCode (dstType srcType : ValType) (x y i j n : Nat) : List AdminInstr :=
  let forward := i ≤ j
  let dst := if forward then i else i + n - 1
  let src := if forward then j else j + n - 1
  instructions [.const (Value.ofNat dstType dst), .const (Value.ofNat srcType src),
    .load .i32_8U y {}, .store .i32_8 x {},
    .const (Value.ofNat dstType (if forward then i + 1 else i)),
    .const (Value.ofNat srcType (if forward then j + 1 else j)),
    .const (Value.ofNat (dstType.minAddress srcType) (n - 1)), .memoryCopy x y]

def initCode (type : ValType) (x y i j n : Nat) (byte : Byte) : List AdminInstr :=
  instructions [.const (Value.ofNat type i), .const (Value.ofNat .i32 byte.toNat),
    .store .i32_8 x {}, .const (Value.ofNat type (i + 1)),
    .const (Value.ofNat .i32 (j + 1)), .const (Value.ofNat .i32 (n - 1)), .memoryInit x y]

/-- Exact bulk-memory redexes. Lowering does not mutate memory; subsequent scalar
load/store reductions do. Bounds are checked even when the length is zero.
-/
inductive BulkReduces (store : Store) (state : Frame) :
    List AdminInstr → Store → List AdminInstr → Prop where
  | fill (hm : store.resolveMem? state.module x = some memory)
      (hi : Value.address? memory.type.addrType a = some i) (hv : v.type = .i32)
      (hn : Value.address? memory.type.addrType len = some n)
      (hb : i + n ≤ memory.bytes.size) :
      BulkReduces store state (values [a, v, len] ++ [.instr (.memoryFill x)]) store
        (if n = 0 then [] else fillCode memory.type.addrType x i v n)
  | fillTrap (hm : store.resolveMem? state.module x = some memory)
      (hi : Value.address? memory.type.addrType a = some i) (hv : v.type = .i32)
      (hn : Value.address? memory.type.addrType len = some n)
      (hb : i + n > memory.bytes.size) :
      BulkReduces store state (values [a, v, len] ++ [.instr (.memoryFill x)]) store [.trap]
  | copy (hd : store.resolveMem? state.module x = some dst)
      (hs : store.resolveMem? state.module y = some src)
      (hi : Value.address? dst.type.addrType a = some i)
      (hj : Value.address? src.type.addrType b = some j)
      (hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len = some n)
      (hb : i + n ≤ dst.bytes.size ∧ j + n ≤ src.bytes.size) :
      BulkReduces store state (values [a, b, len] ++ [.instr (.memoryCopy x y)]) store
        (if n = 0 then [] else copyCode dst.type.addrType src.type.addrType x y i j n)
  | copyTrap (hd : store.resolveMem? state.module x = some dst)
      (hs : store.resolveMem? state.module y = some src)
      (hi : Value.address? dst.type.addrType a = some i)
      (hj : Value.address? src.type.addrType b = some j)
      (hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len = some n)
      (hb : i + n > dst.bytes.size ∨ j + n > src.bytes.size) :
      BulkReduces store state (values [a, b, len] ++ [.instr (.memoryCopy x y)]) store [.trap]
  | init (hm : store.resolveMem? state.module x = some memory)
      (hd : store.resolveData? state.module y = some data)
      (hi : Value.address? memory.type.addrType a = some i)
      (hj : Value.address? .i32 b = some j) (hn : Value.address? .i32 len = some n)
      (hb : i + n ≤ memory.bytes.size ∧ j + n ≤ data.bytes.size) :
      BulkReduces store state (values [a, b, len] ++ [.instr (.memoryInit x y)]) store
        (if hzero : n = 0 then [] else
          initCode memory.type.addrType x y i j n (data.bytes[j]'(by omega)))
  | initTrap (hm : store.resolveMem? state.module x = some memory)
      (hd : store.resolveData? state.module y = some data)
      (hi : Value.address? memory.type.addrType a = some i)
      (hj : Value.address? .i32 b = some j) (hn : Value.address? .i32 len = some n)
      (hb : i + n > memory.bytes.size ∨ j + n > data.bytes.size) :
      BulkReduces store state (values [a, b, len] ++ [.instr (.memoryInit x y)]) store [.trap]
  | drop (ha : state.module.dataAddr? y = some address)
      (hd : store.data? address = some data) :
      BulkReduces store state [.instr (.dataDrop y)] (store.dropData address) []

inductive BulkStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : BulkReduces store state es store' es' → BulkStep store state es store' es'
  | context : BulkStep store state es store' es' →
      BulkStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : BulkStep store state body store' body' →
      BulkStep store state [.label n continuation body] store' [.label n continuation body']
  | handler : BulkStep store state body store' body' →
      BulkStep store state [.handler catches body] store' [.handler catches body']
  | frame : BulkStep store inner body store' body' →
      BulkStep store state [.frame n inner body] store' [.frame n inner body']

theorem BulkStep.functions_preserved (h : BulkStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem BulkStep.globals_preserved (h : BulkStep store state es store' es') :
    store'.globals = store.globals := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem BulkStep.memories_preserved (h : BulkStep store state es store' es') :
    store'.mems = store.mems := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem BulkStep.data_count_preserved (h : BulkStep store state es store' es') :
    store'.datas.length = store.datas.length := by
  induction h with
  | redex h => cases h <;> simp [Store.dropData]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm
