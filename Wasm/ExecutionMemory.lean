import Wasm.ExecutionRuntime

namespace Wasm.Execution

inductive MemoryStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | access (ha : state.module.memAddr? x = some address)
      (hm : store.mem? address = some memory)
      (hi : memoryIndex? es = some x)
      (hr : MemoryReduces memory es change es') :
      MemoryStep store state es (store.applyMemory address change) es'
  | context : MemoryStep store state es store' es' →
      MemoryStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : MemoryStep store state body store' body' →
      MemoryStep store state [.label n continuation body] store' [.label n continuation body']
  | handler : MemoryStep store state body store' body' →
      MemoryStep store state [.handler catches body] store' [.handler catches body']
  | frame : MemoryStep store inner body store' body' →
      MemoryStep store state [.frame n inner body] store' [.frame n inner body']

theorem MemoryStep.functions_preserved (h : MemoryStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | access _ _ _ hr => cases hr <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem MemoryStep.globals_preserved (h : MemoryStep store state es store' es') :
    store'.globals = store.globals := by
  induction h with
  | access _ _ _ hr => cases hr <;> rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem MemoryStep.count_preserved (h : MemoryStep store state es store' es') :
    store'.mems.length = store.mems.length := by
  induction h with
  | access _ _ _ hr => cases hr <;> simp [Store.applyMemory, Store.setMemory]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm.Execution
