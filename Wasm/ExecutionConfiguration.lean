import Wasm.ExecutionVectorStepper
import Wasm.ExecutionRuntime
import Wasm.Stepper
import Wasm.ExecutionCalls
import Wasm.ExecutionGlobals
import Wasm.ExecutionMemoryStepper
import Wasm.ExecutionBulkMemoryStepper
import Wasm.ExecutionReferences
import Wasm.ExecutionTableStepper
import Wasm.ExecutionArrays
import Wasm.ExecutionStructures
import Wasm.ExecutionExceptions

namespace Wasm.Execution

structure Configuration where
  store : Store
  frame : Frame
  code : List AdminInstr
  deriving BEq, Repr

def Configuration.toSpec (c : Configuration) : Wasm.Configuration :=
  ⟨c.store.toSpec, c.frame, c.code⟩

def Configuration.ofSpec (c : Wasm.Configuration) : Configuration :=
  ⟨Store.ofSpec c.store, c.frame, c.code⟩

@[simp] theorem Configuration.toSpec_ofSpec (c : Wasm.Configuration) :
    (Configuration.ofSpec c).toSpec = c := by
  cases c; simp [Configuration.ofSpec, Configuration.toSpec]


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

end Wasm.Execution
