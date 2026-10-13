import Wasm.TypeChecking

/-!
Completeness of the value and result wrappers, with the heap-search obligation explicit.
Fuel is shared by every result element; list length does not consume heap-search fuel.
-/
namespace Wasm.Types

/-- Heap search succeeds for declarative matches within the given heap domain. -/
def HeapSearchCompleteOn (ctx : Context) (fuel : Nat) (domain : HeapType → Prop) : Prop :=
  ∀ a b, domain a → domain b → HeapMatches ctx a b →
    (checkHeap fuel ctx a b).isSome = true

/-- Only references impose a heap-domain condition. -/
def ValType.InHeapDomain (domain : HeapType → Prop) : ValType → Prop
  | .ref _ heap => domain heap
  | _ => True

variable {ctx : Context} {fuel : Nat} {domain : HeapType → Prop}

/-- Positive fuel suffices for heap identity, including rolled recursive types. -/
theorem checkHeap_refl (heap : HeapType) :
    (checkHeap (fuel + 1) ctx heap heap).isSome = true := by
  simp [checkHeap, searchHeap, Search.toOption]

/-- Value completeness reduces solely to heap completeness and declarative nullability. -/
theorem checkVal_complete_of_heap
    (complete : HeapSearchCompleteOn ctx fuel domain)
    {a b : ValType} (matched : ValMatches ctx a b)
    (left : a.InHeapDomain domain) (right : b.InHeapDomain domain) :
    (checkVal fuel ctx a b).isSome = true := by
  cases matched with
  | i32 | i64 | f32 | f64 | v128 | bot =>
    simp [checkVal, searchVal, Search.toOption]
  | @ref _ a b matched =>
    cases a with
    | mk na ha =>
      cases b with
      | mk nb hb =>
        cases matched with
        | mk nullable heap =>
          change (na = true → nb = true) at nullable
          have success := complete ha hb left right heap
          cases found : searchHeap fuel ctx ha hb <;>
            simp [checkHeap, found, Search.toOption] at success
          simp only [checkVal, RefType.val, searchVal]
          rw [dif_pos nullable]
          simp [found, Search.map, Search.toOption]

/-- Numeric and bottom matching is complete even at zero heap-search fuel. -/
theorem checkVal_complete_numbers {a b : ValType} (matched : ValMatches ctx a b)
    (left : a.InHeapDomain (fun _ => False))
    (right : b.InHeapDomain (fun _ => False)) :
    (checkVal fuel ctx a b).isSome = true :=
  checkVal_complete_of_heap (fun _ _ impossible _ _ => False.elim impossible)
    matched left right

/-- Result-list checking introduces no additional matching or fuel obligation. -/
theorem checkResults_complete_of_heap
    (complete : HeapSearchCompleteOn ctx fuel domain)
    {as bs : List ValType} (matched : ResultMatches ctx as bs)
    (left : ∀ a ∈ as, a.InHeapDomain domain)
    (right : ∀ b ∈ bs, b.InHeapDomain domain) :
    (checkResults fuel ctx as bs).isSome = true := by
  induction as generalizing bs with
  | nil => cases matched; rfl
  | cons a as ih =>
    cases matched with
    | @cons _ _ b _ bs head tail =>
      have h := checkVal_complete_of_heap complete head (left _ (by simp)) (right _ (by simp))
      have t := ih tail (fun a member => left a (by simp [member]))
        (fun b member => right b (by simp [member]))
      cases hc : checkVal fuel ctx a b <;> simp [hc] at h
      cases tc : checkResults fuel ctx as bs <;> simp [tc] at t
      simp [checkResults, hc, tc]

/-- All value identities are found with positive fuel, without a runtime validity assumption. -/
theorem checkVal_refl (type : ValType) :
    (checkVal (fuel + 1) ctx type type).isSome = true := by
  cases type <;> simp [checkVal, searchVal, searchHeap, Search.map, Search.toOption]

/-- Exact signature identity is found independently of signature length. -/
theorem checkResults_refl (types : List ValType) :
    (checkResults (fuel + 1) ctx types types).isSome = true := by
  induction types with
  | nil => rfl
  | cons type types ih =>
    have h := checkVal_refl (ctx := ctx) (fuel := fuel) type
    cases hc : checkVal (fuel + 1) ctx type type <;> simp [hc] at h
    cases tc : checkResults (fuel + 1) ctx types types <;> simp [tc] at ih
    simp [checkResults, hc, tc]

#print axioms checkVal_complete_of_heap
#print axioms checkResults_complete_of_heap
#print axioms checkResults_refl

end Wasm.Types
