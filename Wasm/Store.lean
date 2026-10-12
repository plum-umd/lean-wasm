import Wasm.ConfigurationSemantics

/-! Array-backed struct storage. Specification conversion is a boundary operation. -/
namespace Wasm.Execution

structure Store where
  funcs : List FuncInst := []
  globals : List GlobalInst := []
  mems : List MemoryInst := []
  datas : List DataInst := []
  tables : List TableInst := []
  elems : List ElemInst := []
  tags : List TagInst := []
  exns : List ExnInst := []
  structs : Array StructInst := #[]
  arrays : List ArrayInst := []
  deriving BEq, Repr


def Store.toSpec (store : Store) : Wasm.Store :=
  {funcs := store.funcs,
    globals := store.globals,
    mems := store.mems,
    datas := store.datas,
    tables := store.tables,
    elems := store.elems,
    tags := store.tags,
    exns := store.exns,
    structs := store.structs.toList,
    arrays := store.arrays }

def Store.ofSpec (store : Wasm.Store) : Store :=
  {funcs := store.funcs,
    globals := store.globals,
    mems := store.mems,
    datas := store.datas,
    tables := store.tables,
    elems := store.elems,
    tags := store.tags,
    exns := store.exns,
    structs := store.structs.toArray,
    arrays := store.arrays }

def Store.Rel (fast : Store) (spec : Wasm.Store) : Prop := fast.toSpec = spec

@[simp] theorem Store.toSpec_ofSpec (s : Wasm.Store) : (Store.ofSpec s).toSpec = s := by
  cases s; simp [Store.toSpec, Store.ofSpec]

@[simp] theorem Store.ofSpec_toSpec (s : Store) : Store.ofSpec s.toSpec = s := by
  cases s; simp [Store.toSpec, Store.ofSpec]

def Store.func? (store : Store) (address : FuncAddr) : Option FuncInst :=
  store.funcs[address.index]?

def Store.resolveFunc? (store : Store) (module : ModuleInst) (index : Nat) : Option FuncInst :=
  (module.funcAddr? index).bind store.func?

def Store.allocateFunc (store : Store) (function : FuncInst) : FuncAddr × Store :=
  (⟨store.funcs.length⟩, { store with funcs := store.funcs ++ [function] })

def Store.struct? (store : Store) (address : StructAddr) : Option StructInst :=
  store.structs[address.index]?

def Store.array? (store : Store) (address : ArrayAddr) : Option ArrayInst :=
  store.arrays[address.index]?

def Store.allocateStruct (store : Store) (object : StructInst) : StructAddr × Store :=
  let structs := store.structs.push object
  (⟨structs.size - 1⟩, {store with structs})

def Store.global? (store : Store) (address : GlobalAddr) : Option GlobalInst :=
  store.globals[address.index]?

def Store.resolveGlobal? (store : Store) (module : ModuleInst) (index : Nat) : Option GlobalInst :=
  (module.globalAddr? index).bind store.global?

def Store.setGlobal (store : Store) (address : GlobalAddr) (global : GlobalInst) : Store :=
  { store with globals := store.globals.set address.index global }

def Store.mem? (store : Store) (address : MemAddr) : Option MemoryInst := store.mems[address.index]?

def Store.resolveMem? (store : Store) (module : ModuleInst) (index : Nat) : Option MemoryInst :=
  (module.memAddr? index).bind store.mem?

def Store.setMemory (store : Store) (address : MemAddr) (memory : MemoryInst) : Store :=
  { store with mems := store.mems.set address.index memory }

def Store.applyMemory (store : Store) (address : MemAddr) (change : Option MemoryInst) : Store :=
  match change with
  | none => store
  | some memory => store.setMemory address memory

def Store.data? (store : Store) (address : DataAddr) : Option DataInst :=
  store.datas[address.index]?

def Store.resolveData? (store : Store) (module : ModuleInst) (index : Nat) : Option DataInst :=
  (module.dataAddr? index).bind store.data?

def Store.dropData (store : Store) (address : DataAddr) : Store :=
  { store with datas := store.datas.set address.index ⟨#[]⟩ }

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

def Store.writeArray (store : Store) (address : ArrayAddr) (object : ArrayInst) : Store :=
  {store with arrays := store.arrays.modify address.index (fun _ => object)}

def Store.writeStruct (store : Store) (address : StructAddr) (object : StructInst) : Store :=
  {store with structs := store.structs.modify address.index (fun _ => object)}


@[simp] theorem Store.struct?_toSpec (s : Store) (a : StructAddr) :
    s.toSpec.struct? a = s.struct? a := by
  simp [Wasm.Store.struct?, Store.struct?, Store.toSpec]

@[simp] theorem Store.allocateStruct_toSpec (s : Store) (o : StructInst) :
    ((s.allocateStruct o).1, (s.allocateStruct o).2.toSpec) =
      s.toSpec.allocateStruct o := by
  simp [Store.allocateStruct, Wasm.Store.allocateStruct, Store.toSpec]

@[simp] theorem Store.allocateStruct_lookup (s : Store) (o : StructInst) :
    (s.allocateStruct o).2.struct? (s.allocateStruct o).1 = some o := by
  simp [Store.allocateStruct, Store.struct?]

theorem Store.allocateStruct_rel (h : Store.Rel fast spec) (o : StructInst) :
    (fast.allocateStruct o).1 = (spec.allocateStruct o).1 ∧
      Store.Rel (fast.allocateStruct o).2 (spec.allocateStruct o).2 := by
  change fast.toSpec = spec at h
  subst spec
  exact Prod.mk.inj (Store.allocateStruct_toSpec fast o)

theorem Store.struct?_rel (h : Store.Rel fast spec) (a : StructAddr) :
    fast.struct? a = spec.struct? a := by
  change fast.toSpec = spec at h
  subst spec
  exact (Store.struct?_toSpec fast a).symm

@[simp] theorem Store.allocateStruct_preserves (s : Store) (o : StructInst)
    (a : StructAddr) (h : a.index < s.structs.size) :
    (s.allocateStruct o).2.struct? a = s.struct? a := by
  simp [Store.allocateStruct, Store.struct?, Array.getElem?_push, h, Nat.ne_of_lt h]

@[simp] theorem Store.writeStruct_toSpec (s : Store) (a : StructAddr) (o : StructInst) :
    (s.writeStruct a o).toSpec = s.toSpec.writeStruct a o := by
  simp [Store.writeStruct, Wasm.Store.writeStruct, Store.toSpec]

@[simp] theorem Store.func?_toSpec (s : Store) (a : FuncAddr) :
    s.toSpec.func? a = s.func? a := rfl

@[simp] theorem Store.array?_toSpec (s : Store) (a : ArrayAddr) :
    s.toSpec.array? a = s.array? a := rfl

@[simp] theorem Store.global?_toSpec (s : Store) (a : GlobalAddr) :
    s.toSpec.global? a = s.global? a := rfl

@[simp] theorem Store.mem?_toSpec (s : Store) (a : MemAddr) :
    s.toSpec.mem? a = s.mem? a := rfl

@[simp] theorem Store.data?_toSpec (s : Store) (a : DataAddr) :
    s.toSpec.data? a = s.data? a := rfl

@[simp] theorem Store.table?_toSpec (s : Store) (a : TableAddr) :
    s.toSpec.table? a = s.table? a := rfl

@[simp] theorem Store.elem?_toSpec (s : Store) (a : ElemAddr) :
    s.toSpec.elem? a = s.elem? a := rfl

@[simp] theorem Store.resolveFunc?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveFunc? m i = s.resolveFunc? m i := rfl

@[simp] theorem Store.resolveGlobal?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveGlobal? m i = s.resolveGlobal? m i := rfl

@[simp] theorem Store.resolveMem?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveMem? m i = s.resolveMem? m i := rfl

@[simp] theorem Store.resolveData?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveData? m i = s.resolveData? m i := rfl

@[simp] theorem Store.resolveTable?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveTable? m i = s.resolveTable? m i := rfl

@[simp] theorem Store.resolveElem?_toSpec (s : Store) (m : ModuleInst) (i : Nat) :
    s.toSpec.resolveElem? m i = s.resolveElem? m i := rfl

@[simp] theorem Store.setGlobal_toSpec (s : Store) (a : GlobalAddr) (o : GlobalInst) :
    (s.setGlobal a o).toSpec = s.toSpec.setGlobal a o := rfl

@[simp] theorem Store.setMemory_toSpec (s : Store) (a : MemAddr) (o : MemoryInst) :
    (s.setMemory a o).toSpec = s.toSpec.setMemory a o := rfl

@[simp] theorem Store.applyMemory_toSpec (s : Store) (a : MemAddr) (o : Option MemoryInst) :
    (s.applyMemory a o).toSpec = s.toSpec.applyMemory a o := by
  cases o <;> rfl

@[simp] theorem Store.dropData_toSpec (s : Store) (a : DataAddr) :
    (s.dropData a).toSpec = s.toSpec.dropData a := rfl

@[simp] theorem Store.setTable_toSpec (s : Store) (a : TableAddr) (o : TableInst) :
    (s.setTable a o).toSpec = s.toSpec.setTable a o := rfl

@[simp] theorem Store.dropElem_toSpec (s : Store) (a : ElemAddr) :
    (s.dropElem a).toSpec = s.toSpec.dropElem a := rfl

@[simp] theorem Store.writeArray_toSpec (s : Store) (a : ArrayAddr) (o : ArrayInst) :
    (s.writeArray a o).toSpec = s.toSpec.writeArray a o := rfl


@[simp] theorem Store.toSpec_funcs (s : Store) : s.toSpec.funcs = s.funcs := rfl

@[simp] theorem Store.toSpec_globals (s : Store) : s.toSpec.globals = s.globals := rfl

@[simp] theorem Store.toSpec_mems (s : Store) : s.toSpec.mems = s.mems := rfl

@[simp] theorem Store.toSpec_datas (s : Store) : s.toSpec.datas = s.datas := rfl

@[simp] theorem Store.toSpec_tables (s : Store) : s.toSpec.tables = s.tables := rfl

@[simp] theorem Store.toSpec_elems (s : Store) : s.toSpec.elems = s.elems := rfl

@[simp] theorem Store.toSpec_tags (s : Store) : s.toSpec.tags = s.tags := rfl

@[simp] theorem Store.toSpec_exns (s : Store) : s.toSpec.exns = s.exns := rfl

@[simp] theorem Store.toSpec_arrays (s : Store) : s.toSpec.arrays = s.arrays := rfl

@[simp] theorem Store.toSpec_structs_length (s : Store) :
    s.toSpec.structs.length = s.structs.size := by simp [Store.toSpec]

@[simp] theorem Store.toSpec_pushStruct (s : Store) (o : StructInst) :
    ({s with structs := s.structs.push o} : Store).toSpec =
      {s.toSpec with structs := s.toSpec.structs ++ [o]} := by
  simp [Store.toSpec]

@[simp] theorem Store.toSpec_arrays_update (s : Store) (objects : List ArrayInst) :
    ({s with arrays := objects} : Store).toSpec = {s.toSpec with arrays := objects} := rfl

@[simp] theorem Store.toSpec_exns_update (s : Store) (objects : List ExnInst) :
    ({s with exns := objects} : Store).toSpec = {s.toSpec with exns := objects} := rfl

end Wasm.Execution
