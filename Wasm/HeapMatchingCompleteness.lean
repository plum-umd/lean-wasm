import Wasm.RuntimeHierarchyNormalization

/-! Completeness at the existing fixed runtime matching budget. -/
namespace Wasm.Types

theorem HeapType.weight_positive (heap : HeapType) : 0 < heap.weight := by
  cases heap <;> simp only [HeapType.weight] <;> omega

private theorem budget_bounds (a b : HeapType) :
    3 ≤ matchingBudget a b ∧ a.weight + 1 ≤ matchingBudget a b := by
  have left := a.weight_positive
  have right := b.weight_positive
  have squared := Nat.le_mul_self (a.weight + b.weight + 1)
  simp only [matchingBudget, Nat.pow_two]
  omega

private theorem nominal_to_abstract {type : DefinedType} {sub : SubType} {upper : AbstractHeap}
    (unrolled : type.unroll? = some sub)
    (matched : sub.body.abstractHeap.matches upper = true) (fuel : Nat) :
    (checkHeap (fuel + 3) {} type.heap upper.heap).isSome = true := by
  cases type with
  | mk group index =>
    cases sub <;> cases upper <;>
      simp [SubType.body, CompType.abstractHeap, AbstractHeap.matches] at matched
    all_goals simp only [DefinedType.heap, AbstractHeap.heap, checkHeap]
    all_goals rw [searchHeap]
    all_goals simp only [reduceCtorEq, ↓reduceDIte]
    all_goals split <;> rename_i expanded
    all_goals have known := expanded
    all_goals simp only [DefinedType.expand?, DefinedType.expandComposite?, unrolled,
      Option.map_some, Option.bind_some, SubType.body, CompType.func?] at known
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals subst_vars
    all_goals simp [searchHeap, CompType.heap, Search.toOption, Search.map]

private theorem abstract_to_nominal {upper : AbstractHeap} {type : DefinedType} {sub : SubType}
    (unrolled : type.unroll? = some sub)
    (matched : upper.matches sub.body.abstractHeap = true)
    (semantic : HeapMatches {} upper.heap type.heap) (fuel : Nat) :
    (checkHeap (fuel + 3) {} upper.heap type.heap).isSome = true := by
  cases upper
  all_goals try { exact False.elim (HeapMatches.positive_not_defined (by trivial) type semantic) }
  all_goals cases type with
    | mk group index =>
      cases sub <;> simp [SubType.body, CompType.abstractHeap, AbstractHeap.matches] at matched
      all_goals simp only [DefinedType.heap, AbstractHeap.heap, checkHeap]
      all_goals rw [searchHeap]
      all_goals simp only [reduceCtorEq, ↓reduceDIte]
      all_goals try { simp [Search.toOption] }
      all_goals try rfl
      all_goals rw [searchHeap]
      all_goals simp only [reduceCtorEq, ↓reduceDIte]
      all_goals split <;> rename_i expanded
      all_goals have known := expanded
      all_goals simp only [DefinedType.expand?, DefinedType.expandComposite?, unrolled,
        Option.map_some, Option.bind_some, SubType.body, CompType.func?] at known
      all_goals simp_all only [Option.some.injEq, reduceCtorEq]
      all_goals subst_vars
      all_goals simp [searchHeap, CompType.heap, Search.toOption, Search.map]

/-- Every declarative match of valid runtime heaps succeeds at the existing fixed budget. -/
theorem checkHeap_complete_runtime {a b : HeapType} (matched : HeapMatches {} a b)
    (left : HeapValid {} a) (right : HeapValid {} b) :
    (checkHeap (matchingBudget a b) {} a b).isSome = true := by
  obtain ⟨source, sourceView⟩ := left.runtime_view
  obtain ⟨target, targetView⟩ := right.runtime_view
  have hierarchy := matched.runtime_hierarchy rfl source target sourceView targetView
  have bounds := budget_bounds a b
  have decomposition : matchingBudget a b = (matchingBudget a b - 3) + 3 := by omega
  cases sourceView with
  | @abstract source =>
    cases targetView with
    | @abstract target =>
      rw [decomposition]
      exact AbstractHeap.matches_search hierarchy {} (matchingBudget source.heap target.heap - 3 + 1)
    | @defined type sub tree unrolled =>
      rw [decomposition]
      exact abstract_to_nominal unrolled hierarchy matched _
  | @defined source sub sourceTree unrolled =>
    cases targetView with
    | @abstract target =>
      rw [decomposition]
      exact nominal_to_abstract unrolled hierarchy _
    | @defined target targetSub targetTree targetUnrolled =>
      obtain ⟨length, path⟩ := matched.normalize_defined_tree sourceTree.nominal
      have lengthBound := path.length_le_weight sourceTree
      exact path.complete_at (by omega)

/-- On valid runtime heaps, success and declarative matching coincide. -/
theorem checkHeap_runtime_iff {a b : HeapType} (left : HeapValid {} a) (right : HeapValid {} b) :
    (checkHeap (matchingBudget a b) {} a b).isSome = true ↔ HeapMatches {} a b := by
  constructor
  · intro success
    obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp success
    exact proof.down
  · exact fun matched => checkHeap_complete_runtime matched left right

#print axioms checkHeap_complete_runtime
#print axioms checkHeap_runtime_iff

end Wasm.Types
