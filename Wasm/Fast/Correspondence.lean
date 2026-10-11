import Wasm.Fast.Configuration

/-! Correspondence to the unchanged reduction semantics. All decoding here is erased. -/
namespace Wasm.Fast

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

@[simp] theorem evalVectorMemory_toSpec (s : Store) (f : Frame) (op : VectorOp)
    (args : List Value) :
    Wasm.evalVectorMemory s.toSpec f op args = evalVectorMemory s f op args := rfl

@[simp] theorem vectorMemoryStore_toSpec (s : Store) (w : Option (MemAddr × MemoryInst)) :
    (vectorMemoryStore s w).toSpec = Wasm.vectorMemoryStore s.toSpec w := by
  cases w <;> rfl

theorem ArrayNull.toSpec (h : ArrayNull op args) : Wasm.ArrayNull op args := by
  cases h <;> constructor

theorem ArrayAccess.toSpec (h : ArrayAccess s f x a o field) :
    Wasm.ArrayAccess s.toSpec f x a o field := by
  cases h with
  | mk type ht hf ho hm =>
    exact .mk type ht hf (by simpa using ho) ((typed_toSpec _ _ _).mpr hm)

theorem CatchOutcome.toSpec (h : CatchOutcome f a e catches code) :
    Wasm.CatchOutcome f a e catches code := by
  induction h with
  | empty => exact .empty
  | hit ht => exact .hit ht
  | miss ht hne _ ih => exact .miss ht hne ih
  | all => exact .all

macro "transfer_fast " ctor:term : tactic =>
  `(tactic| (first | apply $ctor | (simp; apply $ctor)) <;>
    (first | assumption | (simp_all; done) |
      solve_by_elim [ArrayAccess.toSpec, ArrayNull.toSpec, CatchOutcome.toSpec] | omega))

theorem StructReduces.toSpec (h : StructReduces s f code next code') :
    Wasm.StructReduces s.toSpec f code next.toSpec code' := by
  cases h with
  | new =>
    transfer_fast Wasm.StructReduces.new
  | newDefault =>
    transfer_fast Wasm.StructReduces.newDefault
  | getNull =>
    transfer_fast Wasm.StructReduces.getNull
  | get ht hf hs ho hr hv hu =>
    exact .get ht hf hs (by simpa using ho) ((typed_toSpec _ _ _).mpr hr) hv hu
  | setNull =>
    transfer_fast Wasm.StructReduces.setNull
  | set =>
    transfer_fast Wasm.StructReduces.set

theorem ArrayReduces.toSpec (h : ArrayReduces s f op args next code) :
    Wasm.ArrayReduces s.toSpec f op args next.toSpec code := by
  cases h with
  | null =>
    transfer_fast Wasm.ArrayReduces.null
  | new =>
    transfer_fast Wasm.ArrayReduces.new
  | newDefault =>
    transfer_fast Wasm.ArrayReduces.newDefault
  | newFixed =>
    transfer_fast Wasm.ArrayReduces.newFixed
  | len =>
    transfer_fast Wasm.ArrayReduces.len
  | get =>
    transfer_fast Wasm.ArrayReduces.get
  | getBounds =>
    transfer_fast Wasm.ArrayReduces.getBounds
  | set =>
    transfer_fast Wasm.ArrayReduces.set
  | setBounds =>
    transfer_fast Wasm.ArrayReduces.setBounds
  | fill =>
    transfer_fast Wasm.ArrayReduces.fill
  | fillBounds =>
    transfer_fast Wasm.ArrayReduces.fillBounds
  | copy =>
    transfer_fast Wasm.ArrayReduces.copy
  | copyBounds =>
    transfer_fast Wasm.ArrayReduces.copyBounds
  | newData =>
    transfer_fast Wasm.ArrayReduces.newData
  | newDataBounds =>
    transfer_fast Wasm.ArrayReduces.newDataBounds
  | initData =>
    transfer_fast Wasm.ArrayReduces.initData
  | initDataBounds =>
    transfer_fast Wasm.ArrayReduces.initDataBounds
  | newElem =>
    transfer_fast Wasm.ArrayReduces.newElem
  | newElemBounds =>
    transfer_fast Wasm.ArrayReduces.newElemBounds
  | initElem =>
    transfer_fast Wasm.ArrayReduces.initElem
  | initElemBounds =>
    transfer_fast Wasm.ArrayReduces.initElemBounds

theorem ReferenceReduces.toSpec (h : ReferenceReduces s f code code') :
    Wasm.ReferenceReduces s.toSpec f code code' := by
  cases h with
  | testYes =>
    transfer_fast Wasm.ReferenceReduces.testYes
  | testNo =>
    transfer_fast Wasm.ReferenceReduces.testNo
  | castSource =>
    transfer_fast Wasm.ReferenceReduces.castSource
  | castSourceTrap =>
    transfer_fast Wasm.ReferenceReduces.castSourceTrap
  | brCastYes =>
    transfer_fast Wasm.ReferenceReduces.brCastYes
  | brCastNo =>
    transfer_fast Wasm.ReferenceReduces.brCastNo
  | gc =>
    transfer_fast Wasm.ReferenceReduces.gc
  | null =>
    transfer_fast Wasm.ReferenceReduces.null
  | func =>
    transfer_fast Wasm.ReferenceReduces.func
  | isNull =>
    transfer_fast Wasm.ReferenceReduces.isNull
  | asNonNullTrap =>
    transfer_fast Wasm.ReferenceReduces.asNonNullTrap
  | asNonNull =>
    transfer_fast Wasm.ReferenceReduces.asNonNull
  | brOnNull =>
    transfer_fast Wasm.ReferenceReduces.brOnNull
  | brOnNullFallthrough =>
    transfer_fast Wasm.ReferenceReduces.brOnNullFallthrough
  | brOnNonNullFallthrough =>
    transfer_fast Wasm.ReferenceReduces.brOnNonNullFallthrough
  | brOnNonNull =>
    transfer_fast Wasm.ReferenceReduces.brOnNonNull
  | castLegacy =>
    transfer_fast Wasm.ReferenceReduces.castLegacy
  | castLegacyTrap =>
    transfer_fast Wasm.ReferenceReduces.castLegacyTrap
  | castDefined =>
    transfer_fast Wasm.ReferenceReduces.castDefined
  | castDefinedTrap =>
    transfer_fast Wasm.ReferenceReduces.castDefinedTrap

theorem VectorReduces.toSpec (h : VectorReduces s f code next code') :
    Wasm.VectorReduces s.toSpec f code next.toSpec code' := by
  cases h with
  | pure =>
    transfer_fast Wasm.VectorReduces.pure
  | memory =>
    transfer_fast Wasm.VectorReduces.memory

theorem GlobalStep.toSpec (h : GlobalStep s f code next code') :
    Wasm.GlobalStep s.toSpec f code next.toSpec code' := by
  induction h with
  | get =>
    transfer_fast Wasm.GlobalStep.get
  | set =>
    transfer_fast Wasm.GlobalStep.set
  | context =>
    transfer_fast Wasm.GlobalStep.context
  | label =>
    transfer_fast Wasm.GlobalStep.label
  | handler =>
    transfer_fast Wasm.GlobalStep.handler
  | frame =>
    transfer_fast Wasm.GlobalStep.frame

theorem CallStep.toSpec (h : CallStep s f code code') :
    Wasm.CallStep s.toSpec f code code' := by
  induction h with
  | call =>
    transfer_fast Wasm.CallStep.call
  | callRef =>
    transfer_fast Wasm.CallStep.callRef
  | indirect =>
    transfer_fast Wasm.CallStep.indirect
  | indirectTyped =>
    transfer_fast Wasm.CallStep.indirectTyped
  | returnCall =>
    transfer_fast Wasm.CallStep.returnCall
  | returnCallRef =>
    transfer_fast Wasm.CallStep.returnCallRef
  | returnIndirect =>
    transfer_fast Wasm.CallStep.returnIndirect
  | returnIndirectTyped =>
    transfer_fast Wasm.CallStep.returnIndirectTyped
  | refNull =>
    transfer_fast Wasm.CallStep.refNull
  | refInvoke =>
    transfer_fast Wasm.CallStep.refInvoke
  | invoke =>
    transfer_fast Wasm.CallStep.invoke
  | typedNull =>
    transfer_fast Wasm.CallStep.typedNull
  | typedInvoke =>
    transfer_fast Wasm.CallStep.typedInvoke
  | returnRefNull =>
    transfer_fast Wasm.CallStep.returnRefNull
  | returnRefInvoke =>
    transfer_fast Wasm.CallStep.returnRefInvoke
  | returnInvoke =>
    transfer_fast Wasm.CallStep.returnInvoke
  | returnTypedNull =>
    transfer_fast Wasm.CallStep.returnTypedNull
  | returnTypedInvoke =>
    transfer_fast Wasm.CallStep.returnTypedInvoke
  | tailLabel =>
    transfer_fast Wasm.CallStep.tailLabel
  | tailHandler =>
    transfer_fast Wasm.CallStep.tailHandler
  | tailFrame =>
    transfer_fast Wasm.CallStep.tailFrame
  | context =>
    transfer_fast Wasm.CallStep.context
  | label =>
    transfer_fast Wasm.CallStep.label
  | handler =>
    transfer_fast Wasm.CallStep.handler
  | frame =>
    transfer_fast Wasm.CallStep.frame

theorem MemoryStep.toSpec (h : MemoryStep s f code next code') :
    Wasm.MemoryStep s.toSpec f code next.toSpec code' := by
  induction h with
  | access =>
    transfer_fast Wasm.MemoryStep.access
  | context =>
    transfer_fast Wasm.MemoryStep.context
  | label =>
    transfer_fast Wasm.MemoryStep.label
  | handler =>
    transfer_fast Wasm.MemoryStep.handler
  | frame =>
    transfer_fast Wasm.MemoryStep.frame

theorem BulkReduces.toSpec (h : BulkReduces s f code next code') :
    Wasm.BulkReduces s.toSpec f code next.toSpec code' := by
  cases h with
  | fill =>
    transfer_fast Wasm.BulkReduces.fill
  | fillTrap =>
    transfer_fast Wasm.BulkReduces.fillTrap
  | copy =>
    transfer_fast Wasm.BulkReduces.copy
  | copyTrap =>
    transfer_fast Wasm.BulkReduces.copyTrap
  | init =>
    transfer_fast Wasm.BulkReduces.init
  | initTrap =>
    transfer_fast Wasm.BulkReduces.initTrap
  | drop =>
    transfer_fast Wasm.BulkReduces.drop

theorem TableReduces.toSpec (h : TableReduces s f code next code') :
    Wasm.TableReduces s.toSpec f code next.toSpec code' := by
  cases h with
  | get =>
    transfer_fast Wasm.TableReduces.get
  | getTrap =>
    transfer_fast Wasm.TableReduces.getTrap
  | set =>
    transfer_fast Wasm.TableReduces.set
  | setTrap =>
    transfer_fast Wasm.TableReduces.setTrap
  | size =>
    transfer_fast Wasm.TableReduces.size
  | grow =>
    transfer_fast Wasm.TableReduces.grow
  | growFailure =>
    transfer_fast Wasm.TableReduces.growFailure
  | fill =>
    transfer_fast Wasm.TableReduces.fill
  | fillTrap =>
    transfer_fast Wasm.TableReduces.fillTrap
  | copy =>
    transfer_fast Wasm.TableReduces.copy
  | copyTrap =>
    transfer_fast Wasm.TableReduces.copyTrap
  | init =>
    transfer_fast Wasm.TableReduces.init
  | initTrap =>
    transfer_fast Wasm.TableReduces.initTrap
  | drop =>
    transfer_fast Wasm.TableReduces.drop

theorem ExceptionStep.toSpec (h : ExceptionStep s f code next code') :
    Wasm.ExceptionStep s.toSpec f code next.toSpec code' := by
  induction h with
  | enter =>
    transfer_fast Wasm.ExceptionStep.enter
  | throw_ =>
    transfer_fast Wasm.ExceptionStep.throw_
  | throwRef =>
    transfer_fast Wasm.ExceptionStep.throwRef
  | throwNull =>
    transfer_fast Wasm.ExceptionStep.throwNull
  | discard =>
    transfer_fast Wasm.ExceptionStep.discard
  | labelThrow =>
    transfer_fast Wasm.ExceptionStep.labelThrow
  | frameThrow =>
    transfer_fast Wasm.ExceptionStep.frameThrow
  | caught =>
    transfer_fast Wasm.ExceptionStep.caught
  | done =>
    transfer_fast Wasm.ExceptionStep.done
  | trap =>
    transfer_fast Wasm.ExceptionStep.trap
  | return_ =>
    transfer_fast Wasm.ExceptionStep.return_
  | branch =>
    transfer_fast Wasm.ExceptionStep.branch
  | context =>
    transfer_fast Wasm.ExceptionStep.context
  | label =>
    transfer_fast Wasm.ExceptionStep.label
  | handler =>
    transfer_fast Wasm.ExceptionStep.handler
  | frame =>
    transfer_fast Wasm.ExceptionStep.frame

theorem StructStep.toSpec (h : StructStep s f code next code') :
    Wasm.StructStep s.toSpec f code next.toSpec code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

theorem ArrayStep.toSpec (h : ArrayStep s f code next code') :
    Wasm.ArrayStep s.toSpec f code next.toSpec code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

theorem ReferenceStep.toSpec (h : ReferenceStep s f code code') :
    Wasm.ReferenceStep s.toSpec f code code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

theorem VectorStep.toSpec (h : VectorStep s f code next code') :
    Wasm.VectorStep s.toSpec f code next.toSpec code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

theorem BulkStep.toSpec (h : BulkStep s f code next code') :
    Wasm.BulkStep s.toSpec f code next.toSpec code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

theorem TableStep.toSpec (h : TableStep s f code next code') :
    Wasm.TableStep s.toSpec f code next.toSpec code' := by
  induction h with
  | redex h => exact .redex h.toSpec
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih


theorem ConfigStep.toSpec (h : ConfigStep c next) :
    Wasm.ConfigStep c.toSpec next.toSpec := by
  cases h with
  | vectors h => exact .vectors h.toSpec
  | arrays h => exact .arrays h.toSpec
  | structures h => exact .structures h.toSpec
  | exceptions h => exact .exceptions h.toSpec
  | pure h => exact .pure h
  | locals h => exact .locals h
  | call h => exact .call h.toSpec
  | globals h => exact .globals h.toSpec
  | memory h => exact .memory h.toSpec
  | references h => exact .references h.toSpec
  | tables h => exact .tables h.toSpec
  | bulk h => exact .bulk h.toSpec

theorem ConfigSteps.toSpec (h : ConfigSteps c final) :
    Wasm.ConfigSteps c.toSpec final.toSpec := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons h.toSpec ih

/-- Each successful fast step is one step of the existing specification. -/
theorem stepConfiguration_spec (h : stepConfiguration c = some next) :
    Wasm.ConfigStep c.toSpec next.toSpec := (stepConfiguration_sound h).toSpec

/-- Execution follows the unchanged specification; the array heap is decoded only in proofs. -/
theorem runConfiguration_spec :
    Wasm.ConfigSteps c.toSpec (runConfiguration fuel c).state.toSpec :=
  (runConfiguration_sound).toSpec

end Wasm.Fast
