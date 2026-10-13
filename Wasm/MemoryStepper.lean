import Wasm.Memory
import Wasm.FamilyScanner

namespace Wasm

abbrev CheckedMemoryStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // MemoryStep store state es next.1 next.2 }

private def withMemory (store : Store) (state : Frame) (x : Nat) (es : List AdminInstr)
    (f : (address : MemAddr) → (memory : MemoryInst) →
      state.module.memAddr? x = some address → store.mem? address = some memory →
      CheckedMemoryStep store state es) : CheckedMemoryStep store state es :=
  match ha : state.module.memAddr? x with
  | none => none
  | some address => match hm : store.mem? address with
    | none => none
    | some memory => f address memory ha hm

private def memoryResult (ha : state.module.memAddr? x = some address)
    (hm : store.mem? address = some memory) (hi : memoryIndex? es = some x)
    (hr : MemoryReduces memory es change es') : CheckedMemoryStep store state es :=
  some ⟨(store.applyMemory address change, es'), .access ha hm hi hr⟩

private def checkedMemoryRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedMemoryStep store state es := by
  match es with
  | [.instr (.const a), .instr (.load op x arg)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType a with
      | none => exact none
      | some n =>
        if hb : n + arg.offset + op.bytes ≤ memory.bytes.size then
          exact memoryResult ha hm rfl (.load hn hb)
        else exact memoryResult ha hm rfl (.loadTrap hn (by omega))
  | [.instr (.const a), .instr (.const v), .instr (.store op x arg)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType a with
      | none => exact none
      | some n =>
        if ht : v.type = op.type then
          if hb : n + arg.offset + op.bytes ≤ memory.bytes.size then
            exact memoryResult ha hm rfl (.store hn ht hb)
          else exact memoryResult ha hm rfl (.storeTrap hn ht (by omega))
        else exact none
  | [.instr (.memorySize x)] =>
    exact withMemory store state x _ fun _ _ ha hm => memoryResult ha hm rfl .size
  | [.instr (.const v), .instr (.memoryGrow x)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType v with
      | none => exact none
      | some delta =>
        match hg : memory.grow? delta with
        | none => exact memoryResult ha hm rfl (.growFail hn)
        | some next =>
          exact some ⟨(store.applyMemory address (some next),
            values [Value.ofNat memory.type.addrType memory.pages]), by
              obtain ⟨hcan, he⟩ := MemoryInst.grow?_sound hg
              subst next
              exact .access ha hm rfl (.grow (x := x) hn hcan)⟩
  | _ => exact none

private def memoryOperands : Frame → AdminInstr → Option Nat
  | _, .instr (.load _ _ _) | _, .instr (.memoryGrow _) => some 1
  | _, .instr (.store _ _ _) => some 2
  | _, .instr (.memorySize _) => some 0
  | _, _ => none

private def memoryScanner : FamilyScanner :=
  ⟨memoryOperands, fun store state op args =>
    (checkedMemoryRedex store state (values args ++ [op])).map Subtype.val⟩

private theorem memory_family (step : FamilyStep
    (fun store state op args next code =>
      MemoryStep store state (values args ++ [op]) next code) store state code next code') :
    MemoryStep store state code next code' := by
  induction step with
  | redex reduced => exact reduced
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem memoryScanner_sound (success : memoryScanner.scan store state code [] = some next) :
    MemoryStep store state code next.1 next.2 := by
  apply memory_family
  have localSound : ∀ store state op args next,
      memoryScanner.reduce store state op args = some next →
      MemoryStep store state (values args ++ [op]) next.1 next.2 := by
    intro store state op args next found
    obtain ⟨checked, lookup, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact checked.property
  simpa [values] using memoryScanner.scan_sound localSound success

/-- The shared scanner carries the same certified memory-family result. -/
def checkedMemoryStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedMemoryStep store state code :=
  match found : memoryScanner.scan store state code [] with
  | none => none
  | some next => some ⟨next, memoryScanner_sound found⟩

def stepMemory (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) :=
  (checkedMemoryStep store state es).map Subtype.val

theorem stepMemory_sound (h : stepMemory store state es = some next) :
    MemoryStep store state es next.1 next.2 := by
  unfold stepMemory at h
  cases hs : checkedMemoryStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

private theorem memory_redex_complete
    (ha : state.module.memAddr? x = some address) (hm : store.mem? address = some memory)
    (hi : memoryIndex? code = some x) (reduced : MemoryReduces memory code change code') :
    (checkedMemoryRedex store state code).isSome = true := by
  cases reduced <;> simp only [memoryIndex?, Option.some.injEq] at hi
  all_goals subst x
  all_goals simp only [checkedMemoryRedex, withMemory]
  all_goals split <;> rename_i lookup
  all_goals have known := lookup
  all_goals simp only [ha, Option.some.injEq, reduceCtorEq] at known
  all_goals try contradiction
  all_goals subst_vars
  all_goals split <;> rename_i lookup
  all_goals have known := lookup
  all_goals simp only [hm, Option.some.injEq, reduceCtorEq] at known
  all_goals try contradiction
  all_goals subst_vars
  all_goals simp_all only [memoryResult, Option.isSome_some]
  all_goals repeat first
    | (split <;> rename_i lookup)
    | simp_all

private def MemoryLocal (store : Store) (state : Frame) (op : AdminInstr) (args : List Value)
    (next : Store) (code : List AdminInstr) : Prop :=
  op.ScannerAtom ∧ memoryOperands state op = some args.length ∧
    ∃ x address memory change, state.module.memAddr? x = some address ∧
      store.mem? address = some memory ∧ memoryIndex? (values args ++ [op]) = some x ∧
      MemoryReduces memory (values args ++ [op]) change code ∧
      next = store.applyMemory address change

private theorem memory_family_one
    (localStep : MemoryLocal store state op [a] next code) :
    FamilyStep MemoryLocal store state [.instr (.const a), op] next code := by
  simpa [values] using FamilyStep.redex localStep

private theorem memory_family_two
    (localStep : MemoryLocal store state op [a, b] next code) :
    FamilyStep MemoryLocal store state [.instr (.const a), .instr (.const b), op] next code := by
  simpa [values] using FamilyStep.redex localStep

private theorem memory_family_zero
    (localStep : MemoryLocal store state op [] next code) :
    FamilyStep MemoryLocal store state [op] next code := by
  simpa [values] using FamilyStep.redex localStep

private theorem MemoryStep.toFamily (step : MemoryStep store state code next code') :
    FamilyStep MemoryLocal store state code next code' := by
  induction step with
  | access ha hm hi reduced =>
    cases reduced
    all_goals first | apply memory_family_one | apply memory_family_two | apply memory_family_zero
    all_goals refine ⟨by trivial, rfl, _, _, _, _, ha, hm, hi, ?_, rfl⟩
    all_goals constructor <;> assumption
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- Memory execution is progress-complete, including the permitted growth-failure alternative. -/
theorem stepMemory_complete (reduced : MemoryStep store state code next code') :
    (stepMemory store state code).isSome = true := by
  have localComplete : ∀ state op args next code, MemoryLocal store state op args next code →
      op.ScannerAtom ∧ memoryScanner.operands state op = some args.length ∧
        (memoryScanner.reduce store state op args).isSome = true := by
    intro state op args next code reduced
    obtain ⟨atom, arity, x, address, memory, change, ha, hm, hi, hr, same⟩ := reduced
    exact ⟨atom, arity, by
      simpa [memoryScanner] using memory_redex_complete ha hm hi hr⟩
  have success := memoryScanner.step_complete localComplete reduced.toFamily
  unfold FamilyScanner.step at success
  unfold stepMemory checkedMemoryStep
  split <;> rename_i found
  · simp [found] at success
  · simp

#print axioms stepMemory_complete

end Wasm
