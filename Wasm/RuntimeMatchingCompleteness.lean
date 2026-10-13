import Wasm.HeapMatchingCompleteness
import Wasm.RuntimeTypeInvariant

/-! Runtime matching completeness on declarative type invariants. -/
namespace Wasm

private def valueBudget : Types.ValType → Types.ValType → Nat
  | .ref _ a, .ref _ b => Types.matchingBudget a b
  | _, _ => 1

private theorem value_search_complete {a b : Types.ValType}
    (left : Types.RuntimeValValid {} a) (right : Types.RuntimeValValid {} b)
    (matched : Types.ValMatches {} a b) :
    ((Types.searchVal (valueBudget a b) {} a b).toOption).isSome = true := by
  cases matched with
  | i32 | i64 | f32 | f64 | v128 | bot =>
    simp [Types.searchVal, Types.Search.toOption]
  | @ref _ a b matched =>
    cases a with
    | mk na ha =>
      cases b with
      | mk nb hb =>
        cases left with
        | number member => simp [Types.RefType.val] at member
        | ref left =>
          cases right with
          | number member => simp [Types.RefType.val] at member
          | ref right =>
            cases matched with
            | mk nullable heaps =>
              change (na = true → nb = true) at nullable
              have success := Types.checkHeap_complete_runtime heaps left right
              unfold Types.checkHeap at success
              cases found : Types.searchHeap (Types.matchingBudget ha hb) {} ha hb <;>
                simp [found, Types.Search.toOption] at success
              simp only [valueBudget, Types.RefType.val, Types.searchVal]
              rw [dif_pos nullable]
              simp [found, Types.Search.map, Types.Search.toOption]

/-- Storage matching uses the same bounded value search as runtime reference matching. -/
def checkRuntimeStorage (a b : Types.StorageType) :
    Types.Checked (Types.StorageMatches {} a b) :=
  match a, b with
  | .i8, .i8 => some ⟨.i8⟩
  | .i16, .i16 => some ⟨.i16⟩
  | .val a, .val b =>
    ((Types.searchVal (valueBudget a b) {} a b).toOption).map fun proof => ⟨.val proof.down⟩
  | _, _ => none

/-- Valid unpacked storage types make every semantic storage match succeed. -/
theorem checkRuntimeStorage_complete {a b : Types.StorageType}
    (left : Types.RuntimeValValid {} a.unpack) (right : Types.RuntimeValValid {} b.unpack)
    (matched : Types.StorageMatches {} a b) : (checkRuntimeStorage a b).isSome = true := by
  cases matched with
  | i8 | i16 => rfl
  | val matched =>
    simpa only [checkRuntimeStorage, Option.isSome_map] using
      value_search_complete left right matched

/-- Valid runtime value types match successfully at the checker's unchanged budget. -/
theorem checkRuntimeVal_complete {a b : ValType}
    (left : Types.RuntimeValValid {} (Types.embedVal a))
    (right : Types.RuntimeValValid {} (Types.embedVal b))
    (matched : Types.ValMatches {} (Types.embedVal a) (Types.embedVal b)) :
    (checkRuntimeVal a b).isSome = true := by
  have complete := value_search_complete left right matched
  cases a <;> cases b <;>
    simpa only [checkRuntimeVal, searchRuntimeVal, Types.embedVal, valueBudget] using complete

/-- Semantic value typing succeeds when stored and expected runtime types are valid. -/
theorem checkValue_complete {store : Store} {value : Value} {type : ValType}
    (storeValid : store.RuntimeTypesValid)
    (targetValid : Types.RuntimeValValid {} (Types.embedVal type))
    (typed : Typed store value type) : (checkValue store value type).isSome = true := by
  obtain ⟨actual, lookup, actualValid, matched⟩ := typed.actual_valid storeValid
  have success := checkRuntimeVal_complete actualValid targetValid matched
  unfold checkRuntimeVal at success
  unfold checkValue searchValue
  split <;> rename_i found
  · simp [lookup] at found
  · have same := found
    rw [lookup] at same
    cases same
    cases checked : searchRuntimeVal actual type <;>
      simp [checked, Types.Search.toOption] at success
    simp [Types.Search.map, Types.Search.toOption]

/-- A positive semantic value match yields a found search result on valid runtime types. -/
theorem searchValue_complete {store : Store} {value : Value} {type : ValType}
    (storeValid : store.RuntimeTypesValid)
    (targetValid : Types.RuntimeValValid {} (Types.embedVal type))
    (typed : Typed store value type) : ∃ proof, searchValue store value type = .found proof := by
  have success := checkValue_complete storeValid targetValid typed
  unfold checkValue at success
  cases found : searchValue store value type <;> simp [found, Types.Search.toOption] at success
  exact ⟨_, rfl⟩

/-- Argument matching is complete under the same declarative runtime invariants. -/
theorem checkArgs_complete {store : Store} {values : List Value} {types : List ValType}
    (storeValid : store.RuntimeTypesValid)
    (targetsValid : ∀ type ∈ types, Types.RuntimeValValid {} (Types.embedVal type))
    (typed : ArgsTyped store values types) : (checkArgs store values types).isSome = true := by
  induction typed with
  | nil => rfl
  | @cons value type values types head tail ih =>
    have headSuccess := checkValue_complete storeValid (targetsValid type (by simp)) head
    have tailSuccess := ih (fun type member => targetsValid type (by simp [member]))
    obtain ⟨headProof, headFound⟩ := Option.isSome_iff_exists.mp headSuccess
    obtain ⟨tailProof, tailFound⟩ := Option.isSome_iff_exists.mp tailSuccess
    simp [checkArgs, headFound, tailFound]

#print axioms checkRuntimeVal_complete
#print axioms checkValue_complete
#print axioms checkArgs_complete

end Wasm
