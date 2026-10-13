import Wasm.TypeMatching

/-! Closed runtime types eliminate closing-equality detours in matching derivations. -/
namespace Wasm.Types

private theorem mapM_fixed {f : α → Option α} {xs : List α}
    (fixed : ∀ x ∈ xs, f x = some x) : xs.mapM f = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, fixed x (by simp), ih (fun x member => fixed x (by simp [member]))]

private theorem scoped_closing_fixed (types : List DefinedType) (fuel : Nat) :
    (∀ recs heap, HeapType.scopedFuel fuel 0 recs heap = true →
      heap.close? types = some heap) ∧
    (∀ recs type, ValType.scopedFuel fuel 0 recs type = true →
      type.close? types = some type) ∧
    (∀ recs storage, StorageType.scopedFuel fuel 0 recs storage = true →
      storage.close? types = some storage) ∧
    (∀ recs field, FieldType.scopedFuel fuel 0 recs field = true →
      field.close? types = some field) ∧
    (∀ recs sub, SubType.scopedFuel fuel 0 recs sub = true →
      sub.close? types = some sub) := by
  induction fuel with
  | zero =>
    simp [HeapType.scopedFuel, ValType.scopedFuel, StorageType.scopedFuel,
      FieldType.scopedFuel, SubType.scopedFuel]
  | succ fuel ih =>
    rcases ih with ⟨heaps, vals, storages, fields, subs⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro recs heap scopeProof
      cases heap <;> simp only [HeapType.scopedFuel] at scopeProof
      all_goals try { simp [HeapType.close?] }
      case typeIdx index => simp at scopeProof
      case defined group index =>
        simp only [Bool.and_eq_true] at scopeProof
        have members := List.all_eq_true.mp scopeProof.2
        have fixed := mapM_fixed (fun sub member => subs group.length sub (members sub member))
        simp [HeapType.close?, fixed]
    · intro recs type scopeProof
      cases type <;> simp only [ValType.scopedFuel] at scopeProof
      all_goals try { simp [ValType.close?] }
      case ref nullable heap => simp [ValType.close?, heaps recs heap scopeProof]
    · intro recs storage scopeProof
      cases storage <;> simp only [StorageType.scopedFuel] at scopeProof
      all_goals try { simp [StorageType.close?] }
      case val type => simp [StorageType.close?, vals recs type scopeProof]
    · intro recs field scopeProof
      cases field with
      | mk storage mutable =>
        simp only [FieldType.scopedFuel] at scopeProof
        simp [FieldType.close?, storages recs storage scopeProof]
    · intro recs sub scopeProof
      cases sub with
      | func final supers params results =>
        simp only [SubType.scopedFuel, Bool.and_eq_true] at scopeProof
        have superFixed := mapM_fixed (fun heap member =>
          heaps recs heap (List.all_eq_true.mp scopeProof.1.1 heap member))
        have paramFixed := mapM_fixed (fun type member =>
          vals recs type (List.all_eq_true.mp scopeProof.1.2 type member))
        have resultFixed := mapM_fixed (fun type member =>
          vals recs type (List.all_eq_true.mp scopeProof.2 type member))
        simp [SubType.close?, superFixed, paramFixed, resultFixed]
      | struct_ final supers fs =>
        simp only [SubType.scopedFuel, Bool.and_eq_true] at scopeProof
        have superFixed := mapM_fixed (fun heap member =>
          heaps recs heap (List.all_eq_true.mp scopeProof.1 heap member))
        have fieldFixed := mapM_fixed (fun field member =>
          fields recs field (List.all_eq_true.mp scopeProof.2 field member))
        simp [SubType.close?, superFixed, fieldFixed]
      | array final supers field =>
        simp only [SubType.scopedFuel, Bool.and_eq_true] at scopeProof
        have superFixed := mapM_fixed (fun heap member =>
          heaps recs heap (List.all_eq_true.mp scopeProof.1 heap member))
        simp [SubType.close?, superFixed, fields recs field scopeProof.2]

/-- Closing cannot change a type whose free type indices are absent. -/
theorem HeapType.close?_of_closed {heap : HeapType} (closed : heap.closed)
    (types : List DefinedType) : heap.close? types = some heap := by
  obtain ⟨fuel, scopeProof⟩ := closed
  exact (scoped_closing_fixed types fuel).1 0 heap scopeProof

/-- Closed rolled types retain their identity under every closing context. -/
theorem DefinedType.close?_of_closed {type : DefinedType} (closed : type.closed)
    (types : List DefinedType) : type.close? types = some type := by
  have fixed := HeapType.close?_of_closed closed types
  cases type with
  | mk group index =>
    simp only [DefinedType.heap, HeapType.close?] at fixed
    cases result : group.mapM (SubType.close? types) <;> simp [result] at fixed
    simp [DefinedType.close?, result, fixed]

/-- Closing equality of closed runtime definitions is ordinary identity. -/
theorem DefinedType.eq_of_close?_eq {a b closed : DefinedType} {types : List DefinedType}
    (leftValid : a.closed) (rightValid : b.closed)
    (left : a.close? types = some closed) (right : b.close? types = some closed) : a = b := by
  rw [a.close?_of_closed leftValid types] at left
  rw [b.close?_of_closed rightValid types] at right
  exact (Option.some.inj left).trans (Option.some.inj right).symm

#print axioms DefinedType.close?_of_closed
#print axioms DefinedType.eq_of_close?_eq

end Wasm.Types
