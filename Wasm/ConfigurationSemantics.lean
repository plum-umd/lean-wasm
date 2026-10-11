import Wasm.VectorStepper
import Wasm.Runtime
import Wasm.Stepper
import Wasm.Calls
import Wasm.Globals
import Wasm.MemoryStepper
import Wasm.BulkMemoryStepper
import Wasm.References
import Wasm.TableStepper
import Wasm.Arrays
import Wasm.Structures
import Wasm.Exceptions

namespace Wasm

/-- Configuration reductions share the store and evaluate in the current frame. -/
inductive ConfigStep : Configuration → Configuration → Prop where
  | vectors (h : VectorStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | arrays (h : ArrayStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | structures (h : StructStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | exceptions (h : ExceptionStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | pure (h : ExecStep frame.module.types code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | locals (h : LocalStep frame code frame' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame', code'⟩
  | call (h : CallStep store frame code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | globals (h : GlobalStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | memory (h : MemoryStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | references (h : ReferenceStep store frame code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | tables (h : TableStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | bulk (h : BulkStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩

inductive ConfigSteps : Configuration → Configuration → Prop where
  | refl : ConfigSteps config config
  | cons : ConfigStep config middle → ConfigSteps middle final → ConfigSteps config final

theorem ConfigStep.functions_preserved (h : ConfigStep config next) :
    next.store.funcs = config.store.funcs := by
  cases h with
  | vectors h => rw [h.resources_preserved.1]
  | arrays h => rw [h.resources_preserved.1]
  | structures h => rw [h.resources_preserved.1]
  | exceptions h => rw [h.resources_preserved.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.functions_preserved
  | memory h => exact h.functions_preserved
  | bulk h => exact h.functions_preserved
  | tables h => exact h.functions_preserved

theorem ConfigStep.module_preserved (h : ConfigStep config next) :
    next.frame.module = config.frame.module := by
  cases h with
  | pure | call | globals | memory | bulk | references | tables | exceptions
    | structures | arrays | vectors => rfl
  | locals h => exact h.module_preserved

theorem ConfigSteps.functions_preserved (h : ConfigSteps config final) :
    final.store.funcs = config.store.funcs := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact ih.trans h.functions_preserved

theorem ConfigStep.global_count_preserved (h : ConfigStep config next) :
    next.store.globals.length = config.store.globals.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.1]
  | arrays h => rw [h.resources_preserved.2.1]
  | structures h => rw [h.resources_preserved.2.1]
  | exceptions h => rw [h.resources_preserved.2.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.length_preserved
  | memory h => rw [h.globals_preserved]
  | bulk h => rw [h.globals_preserved]
  | tables h => rw [h.globals_preserved]

theorem ConfigStep.global_types_preserved (h : ConfigStep config next) :
    next.store.globals.map GlobalInst.type = config.store.globals.map GlobalInst.type := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.1]
  | arrays h => rw [h.resources_preserved.2.1]
  | structures h => rw [h.resources_preserved.2.1]
  | exceptions h => rw [h.resources_preserved.2.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.types_preserved
  | memory h => rw [h.globals_preserved]
  | bulk h => rw [h.globals_preserved]
  | tables h => rw [h.globals_preserved]

theorem ConfigStep.memory_count_preserved (h : ConfigStep config next) :
    next.store.mems.length = config.store.mems.length := by
  cases h with
  | vectors h => exact h.resources_preserved.2.2.1
  | arrays h => rw [h.resources_preserved.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h => exact h.count_preserved
  | bulk h => rw [h.memories_preserved]
  | tables h => rw [h.memories_preserved]

theorem ConfigStep.data_count_preserved (h : ConfigStep config next) :
    next.store.datas.length = config.store.datas.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.1]
  | arrays h => rw [h.resources_preserved.2.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h => exact h.data_count_preserved
  | tables h => exact h.data_count_preserved

theorem ConfigStep.table_count_preserved (h : ConfigStep config next) :
    next.store.tables.length = config.store.tables.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.2.1]
  | arrays h => rw [h.resources_preserved.2.2.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex h => cases h <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h => exact h.table_count_preserved

theorem ConfigStep.elem_count_preserved (h : ConfigStep config next) :
    next.store.elems.length = config.store.elems.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.2.2]
  | arrays h => rw [h.resources_preserved.2.2.2.2.2]
  | structures h => rw [h.resources_preserved.2.2.2.2.2]
  | exceptions h => rw [h.resources_preserved.2.2.2.2.2]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex h => cases h <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h => exact h.elem_count_preserved

end Wasm
