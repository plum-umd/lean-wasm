import Wasm.BulkMemory
import Wasm.FamilyScanner

namespace Wasm

abbrev CheckedBulkStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // BulkStep store state es next.1 next.2 }

private def bulkResult (h : BulkReduces store state es store' es') :
    CheckedBulkStep store state es := some ⟨(store', es'), .redex h⟩

private def checkedBulkRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedBulkStep store state es := by
  match es with
  | [.instr (.const a), .instr (.const v), .instr (.const len), .instr (.memoryFill x)] =>
    match hm : store.resolveMem? state.module x with
    | none => exact none
    | some memory =>
      match hi : Value.address? memory.type.addrType a,
          hn : Value.address? memory.type.addrType len with
      | some i, some n =>
        if hv : v.type = .i32 then
          if hb : i + n ≤ memory.bytes.size then
            exact bulkResult (.fill hm hi hv hn hb)
          else exact bulkResult (.fillTrap hm hi hv hn (by omega))
        else exact none
      | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.memoryCopy x y)] =>
    match hd : store.resolveMem? state.module x, hs : store.resolveMem? state.module y with
    | some dst, some src =>
      match hi : Value.address? dst.type.addrType a, hj : Value.address? src.type.addrType b,
          hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len with
      | some i, some j, some n =>
        if hb : i + n ≤ dst.bytes.size ∧ j + n ≤ src.bytes.size then
          exact bulkResult (.copy hd hs hi hj hn hb)
        else exact bulkResult (.copyTrap hd hs hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.memoryInit x y)] =>
    match hm : store.resolveMem? state.module x, hd : store.resolveData? state.module y with
    | some memory, some data =>
      match hi : Value.address? memory.type.addrType a, hj : Value.address? .i32 b,
          hn : Value.address? .i32 len with
      | some i, some j, some n =>
        if hb : i + n ≤ memory.bytes.size ∧ j + n ≤ data.bytes.size then
          exact bulkResult (.init hm hd hi hj hn hb)
        else exact bulkResult (.initTrap hm hd hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.dataDrop y)] =>
    match ha : state.module.dataAddr? y with
    | none => exact none
    | some address =>
      match hd : store.data? address with
      | none => exact none
      | some data => exact bulkResult (.drop ha hd)
  | _ => exact none

private def bulkOperands : Frame → AdminInstr → Option Nat
  | _, .instr (.memoryFill _) | _, .instr (.memoryCopy _ _) | _, .instr (.memoryInit _ _) => some 3
  | _, .instr (.dataDrop _) => some 0
  | _, _ => none

private def bulkScanner : FamilyScanner :=
  ⟨bulkOperands, fun store state op args =>
    (checkedBulkRedex store state (values args ++ [op])).map Subtype.val⟩

private theorem bulk_family (step : FamilyStep
    (fun store state op args next code => BulkStep store state (values args ++ [op]) next code)
    store state code next code') : BulkStep store state code next code' := by
  induction step with
  | redex reduced => exact reduced
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem bulkScanner_sound (success : bulkScanner.scan store state code [] = some next) :
    BulkStep store state code next.1 next.2 := by
  apply bulk_family
  have localSound : ∀ store state op args next,
      bulkScanner.reduce store state op args = some next →
      BulkStep store state (values args ++ [op]) next.1 next.2 := by
    intro store state op args next found
    obtain ⟨checked, lookup, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact checked.property
  simpa [values] using bulkScanner.scan_sound localSound success

def checkedBulkStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedBulkStep store state code :=
  match found : bulkScanner.scan store state code [] with
  | none => none
  | some next => some ⟨next, bulkScanner_sound found⟩

def stepBulkMemory (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedBulkStep store state es).map Subtype.val

theorem stepBulkMemory_sound (h : stepBulkMemory store state es = some next) :
    BulkStep store state es next.1 next.2 := by
  unfold stepBulkMemory at h
  cases hs : checkedBulkStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

private theorem bulk_redex_complete (reduced : BulkReduces store state code next code') :
    (checkedBulkRedex store state code).isSome = true := by
  cases reduced <;> simp only [values, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, checkedBulkRedex]
  all_goals repeat first
    | simp_all [bulkResult]
    | split

private def BulkLocal (store : Store) (state : Frame) (op : AdminInstr) (args : List Value)
    (next : Store) (code : List AdminInstr) : Prop :=
  op.ScannerAtom ∧ bulkOperands state op = some args.length ∧
    BulkReduces store state (values args ++ [op]) next code

private theorem BulkStep.toFamily (step : BulkStep store state code next code') :
    FamilyStep BulkLocal store state code next code' := by
  induction step with
  | redex reduced =>
    cases reduced
    all_goals first
      | refine FamilyStep.redex (args := [_, _, _]) (op := .instr _) ?_
      | refine FamilyStep.redex (args := []) (op := .instr _) ?_
    all_goals refine ⟨by trivial, rfl, ?_⟩
    all_goals constructor <;> assumption
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- Bulk memory execution recognizes every semantic reduction in every evaluation context. -/
theorem stepBulkMemory_complete (reduced : BulkStep store state code next code') :
    (stepBulkMemory store state code).isSome = true := by
  have localComplete : ∀ state op args next code, BulkLocal store state op args next code →
      op.ScannerAtom ∧ bulkScanner.operands state op = some args.length ∧
        (bulkScanner.reduce store state op args).isSome = true := by
    intro state op args next code reduced
    obtain ⟨atom, arity, hr⟩ := reduced
    exact ⟨atom, arity, by simpa [bulkScanner] using bulk_redex_complete hr⟩
  have success := bulkScanner.step_complete localComplete reduced.toFamily
  unfold FamilyScanner.step at success
  unfold stepBulkMemory checkedBulkStep
  split <;> rename_i found
  · simp [found] at success
  · simp

#print axioms stepBulkMemory_complete

end Wasm
