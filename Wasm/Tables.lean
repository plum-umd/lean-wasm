import Wasm.BulkMemory

namespace Wasm

def ModuleInst.tableAddr? (module : ModuleInst) (x : Nat) : Option TableAddr := module.tables[x]?
def ModuleInst.elemAddr? (module : ModuleInst) (x : Nat) : Option ElemAddr := module.elems[x]?
def Store.table? (store : Store) (address : TableAddr) : Option TableInst :=
  store.tables[address.index]?
def Store.elem? (store : Store) (address : ElemAddr) : Option ElemInst :=
  store.elems[address.index]?
def Store.resolveTable? (store : Store) (module : ModuleInst) (x : Nat) : Option TableInst :=
  module.tableAddr? x >>= store.table?
def Store.resolveElem? (store : Store) (module : ModuleInst) (x : Nat) : Option ElemInst :=
  module.elemAddr? x >>= store.elem?
def Store.setTable (store : Store) (address : TableAddr) (table : TableInst) : Store :=
  { store with tables := store.tables.set address.index table }
def Store.dropElem (store : Store) (address : ElemAddr) : Store :=
  { store with elems := store.elems.modify address.index fun elem => { elem with refs := #[] } }

theorem Store.dropElem_lookup {store : Store} {address : ElemAddr} {element : ElemInst}
    (h : store.elem? address = some element) :
    (store.dropElem address).elem? address = some { element with refs := #[] } := by
  simp only [Store.elem?] at h
  simp [Store.dropElem, Store.elem?, h]

def TableType.Valid (type : TableType) : Prop :=
  type.addrType.IsInteger ∧ type.min < 2 ^ type.addrType.bits ∧
    ∀ maximum ∈ type.max, type.min ≤ maximum ∧ maximum < 2 ^ type.addrType.bits
instance instDecidableTableTypeValid (type : TableType) : Decidable type.Valid := by
  unfold TableType.Valid
  infer_instance

def TableInst.grown (table : TableInst) (reference : RefValue) (n : Nat) : TableInst :=
  { type := { table.type with min := table.refs.size + n },
    refs := table.refs ++ Array.replicate n reference }
def TableInst.CanGrow (table : TableInst) (n : Nat) : Prop :=
  table.refs.size + n < 2 ^ table.type.addrType.bits ∧
    ∀ maximum ∈ table.type.max, table.refs.size + n ≤ maximum
instance (table : TableInst) (n : Nat) : Decidable (table.CanGrow n) := by
  unfold TableInst.CanGrow
  infer_instance

def tableGrowthBudget : Nat := 65536

def tableFillCode (type : ValType) (x i : Nat) (v : Value) (n : Nat) : List AdminInstr :=
  instructions [.const (Value.ofNat type i), .const v, .tableSet x,
    .const (Value.ofNat type (i + 1)), .const v, .const (Value.ofNat type (n - 1)),
    .tableFill x]

def tableCopyCode (dstType srcType : ValType) (x y i j n : Nat) : List AdminInstr :=
  let forward := i ≤ j
  let dst := if forward then i else i + n - 1
  let src := if forward then j else j + n - 1
  instructions [.const (Value.ofNat dstType dst), .const (Value.ofNat srcType src),
    .tableGet y, .tableSet x,
    .const (Value.ofNat dstType (if forward then i + 1 else i)),
    .const (Value.ofNat srcType (if forward then j + 1 else j)),
    .const (Value.ofNat (dstType.minAddress srcType) (n - 1)), .tableCopy x y]

def tableInitCode (type : ValType) (x y i j n : Nat) (reference : RefValue) : List AdminInstr :=
  instructions [.const (Value.ofNat type i), .const (.ref reference),
    .tableSet x, .const (Value.ofNat type (i + 1)),
    .const (Value.ofNat .i32 (j + 1)), .const (Value.ofNat .i32 (n - 1)), .tableInit x y]

/-- Exact table redexes. Bulk operations lower to individual table accesses.
Bounds are checked before writes, including when the length is zero.
-/
inductive TableReduces (store : Store) (state : Frame) :
    List AdminInstr → Store → List AdminInstr → Prop where
  | get (ht : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i) (hb : i < table.refs.size) :
      TableReduces store state (values [a] ++ [.instr (.tableGet x)]) store
        (values [.ref (table.refs[i]'hb)])
  | getTrap (ht : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i) (hb : table.refs.size ≤ i) :
      TableReduces store state (values [a] ++ [.instr (.tableGet x)]) store [.trap]
  | set (ha : state.module.tableAddr? x = some address) (ht : store.table? address = some table)
      (hi : Value.address? table.type.addrType a = some i) (hv : Typed store (.ref reference) table.type.refType)
      (hb : i < table.refs.size) :
      TableReduces store state (values [a, .ref reference] ++ [.instr (.tableSet x)])
        (store.setTable address { table with refs := table.refs.set i reference }) []
  | setTrap (ht : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i) (hv : Typed store (.ref reference) table.type.refType)
      (hb : table.refs.size ≤ i) :
      TableReduces store state (values [a, .ref reference] ++ [.instr (.tableSet x)]) store [.trap]
  | size (ht : store.resolveTable? state.module x = some table) :
      TableReduces store state [.instr (.tableSize x)] store
        (values [Value.ofNat table.type.addrType table.refs.size])
  | grow (ha : state.module.tableAddr? x = some address) (ht : store.table? address = some table)
      (hn : Value.address? table.type.addrType len = some n) (hv : Typed store (.ref reference) table.type.refType)
      (hg : table.CanGrow n) :
      TableReduces store state (values [.ref reference, len] ++ [.instr (.tableGrow x)])
        (store.setTable address (table.grown reference n))
        (values [Value.ofNat table.type.addrType table.refs.size])
  | growFailure (ht : store.resolveTable? state.module x = some table)
      (hn : Value.address? table.type.addrType len = some n)
      (hv : Typed store (.ref reference) table.type.refType) :
      TableReduces store state (values [.ref reference, len] ++ [.instr (.tableGrow x)]) store
        (values [Value.ofInt table.type.addrType (-1)])
  | fill (hm : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i) (hv : Typed store v table.type.refType)
      (hn : Value.address? table.type.addrType len = some n)
      (hb : i + n ≤ table.refs.size) :
      TableReduces store state (values [a, v, len] ++ [.instr (.tableFill x)]) store
        (if n = 0 then [] else tableFillCode table.type.addrType x i v n)
  | fillTrap (hm : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i) (hv : Typed store v table.type.refType)
      (hn : Value.address? table.type.addrType len = some n)
      (hb : i + n > table.refs.size) :
      TableReduces store state (values [a, v, len] ++ [.instr (.tableFill x)]) store [.trap]
  | copy (hd : store.resolveTable? state.module x = some dst)
      (hs : store.resolveTable? state.module y = some src)
      (hi : Value.address? dst.type.addrType a = some i)
      (hj : Value.address? src.type.addrType b = some j)
      (hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len = some n)
      (hb : i + n ≤ dst.refs.size ∧ j + n ≤ src.refs.size) :
      TableReduces store state (values [a, b, len] ++ [.instr (.tableCopy x y)]) store
        (if n = 0 then [] else tableCopyCode dst.type.addrType src.type.addrType x y i j n)
  | copyTrap (hd : store.resolveTable? state.module x = some dst)
      (hs : store.resolveTable? state.module y = some src)
      (hi : Value.address? dst.type.addrType a = some i)
      (hj : Value.address? src.type.addrType b = some j)
      (hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len = some n)
      (hb : i + n > dst.refs.size ∨ j + n > src.refs.size) :
      TableReduces store state (values [a, b, len] ++ [.instr (.tableCopy x y)]) store [.trap]
  | init (hm : store.resolveTable? state.module x = some table)
      (hd : store.resolveElem? state.module y = some element)
      (hi : Value.address? table.type.addrType a = some i)
      (hj : Value.address? .i32 b = some j)
      (hn : Value.address? .i32 len = some n)
      (hb : i + n ≤ table.refs.size ∧ j + n ≤ element.refs.size) :
      TableReduces store state (values [a, b, len] ++ [.instr (.tableInit x y)]) store
        (if hzero : n = 0 then [] else
          tableInitCode table.type.addrType x y i j n (element.refs[j]'(by omega)))
  | initTrap (hm : store.resolveTable? state.module x = some table)
      (hd : store.resolveElem? state.module y = some element)
      (hi : Value.address? table.type.addrType a = some i)
      (hj : Value.address? .i32 b = some j)
      (hn : Value.address? .i32 len = some n)
      (hb : i + n > table.refs.size ∨ j + n > element.refs.size) :
      TableReduces store state (values [a, b, len] ++ [.instr (.tableInit x y)]) store [.trap]
  | drop (ha : state.module.elemAddr? y = some address)
      (hd : store.elem? address = some element) :
      TableReduces store state [.instr (.elemDrop y)] (store.dropElem address) []

inductive TableStep :
    Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : TableReduces store state es store' es' → TableStep store state es store' es'
  | context : TableStep store state es store' es' →
      TableStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : TableStep store state body store' body' →
      TableStep store state [.label n continuation body] store' [.label n continuation body']
  | frame : TableStep store inner body store' body' →
      TableStep store state [.frame n inner body] store' [.frame n inner body']

theorem TableStep.functions_preserved (h : TableStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem TableStep.globals_preserved (h : TableStep store state es store' es') :
    store'.globals = store.globals := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem TableStep.memories_preserved (h : TableStep store state es store' es') :
    store'.mems = store.mems := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem TableStep.data_count_preserved (h : TableStep store state es store' es') :
    store'.datas.length = store.datas.length := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem TableStep.table_count_preserved (h : TableStep store state es store' es') :
    store'.tables.length = store.tables.length := by
  induction h with
  | redex h => cases h <;> simp [Store.setTable, Store.dropElem]
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem TableStep.elem_count_preserved (h : TableStep store state es store' es') :
    store'.elems.length = store.elems.length := by
  induction h with
  | redex h => cases h <;> simp [Store.setTable, Store.dropElem]
  | context _ ih | label _ ih | frame _ ih => exact ih

end Wasm
