import Wasm.ExecutionRuntime

namespace Wasm.Execution

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
      (hi : Value.address? table.type.addrType a = some i)
      (hv : Typed store (.ref reference) table.type.refType)
      (hb : i < table.refs.size) :
      TableReduces store state (values [a, .ref reference] ++ [.instr (.tableSet x)])
        (store.setTable address { table with refs := table.refs.set i reference }) []
  | setTrap (ht : store.resolveTable? state.module x = some table)
      (hi : Value.address? table.type.addrType a = some i)
      (hv : Typed store (.ref reference) table.type.refType)
      (hb : table.refs.size ≤ i) :
      TableReduces store state (values [a, .ref reference] ++ [.instr (.tableSet x)]) store [.trap]
  | size (ht : store.resolveTable? state.module x = some table) :
      TableReduces store state [.instr (.tableSize x)] store
        (values [Value.ofNat table.type.addrType table.refs.size])
  | grow (ha : state.module.tableAddr? x = some address) (ht : store.table? address = some table)
      (hn : Value.address? table.type.addrType len = some n)
      (hv : Typed store (.ref reference) table.type.refType)
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
  | handler : TableStep store state body store' body' →
      TableStep store state [.handler catches body] store' [.handler catches body']
  | frame : TableStep store inner body store' body' →
      TableStep store state [.frame n inner body] store' [.frame n inner body']

theorem TableStep.functions_preserved (h : TableStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem TableStep.globals_preserved (h : TableStep store state es store' es') :
    store'.globals = store.globals := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem TableStep.memories_preserved (h : TableStep store state es store' es') :
    store'.mems = store.mems := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem TableStep.data_count_preserved (h : TableStep store state es store' es') :
    store'.datas.length = store.datas.length := by
  induction h with
  | redex h => cases h <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem TableStep.table_count_preserved (h : TableStep store state es store' es') :
    store'.tables.length = store.tables.length := by
  induction h with
  | redex h => cases h <;> simp [Store.setTable, Store.dropElem]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem TableStep.elem_count_preserved (h : TableStep store state es store' es') :
    store'.elems.length = store.elems.length := by
  induction h with
  | redex h => cases h <;> simp [Store.setTable, Store.dropElem]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm.Execution
