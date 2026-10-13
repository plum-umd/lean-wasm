import Wasm.MatchingNormalization
import Wasm.ClosingNormalization

/-! Valid rolled declarations have nominal parents after recursive indices are unrolled. -/
namespace Wasm.Types

private theorem SubType.supers_mapHeap (sub : SubType) (f : HeapType → HeapType) :
    (sub.mapHeap f).supers = sub.supers.map f := by
  cases sub <;> rfl

private theorem RuntimeSuperValid.unrolled_parent_defined {group : RecType} {index : Nat}
    {body : CompType} {parent : HeapType}
    (valid : RuntimeSuperValid {recs := group} index body parent)
    (bound : index < group.length) :
    ∃ type : DefinedType, parent.substRecs (unrollIndex group) = type.heap := by
  cases valid with
  | mk heapValid precedes unrolled nonfinal matched =>
    cases parent <;> simp only [HeapType.unrollIn?] at unrolled
    all_goals try contradiction
    case defined parents i => exact ⟨⟨parents, i⟩, rfl⟩
    case recIdx i =>
      have earlier : i < index := precedes
      have inGroup : i < group.length := Nat.lt_trans earlier bound
      exact ⟨⟨group, i⟩, by simp [HeapType.substRecs, unrollIndex, inGroup, DefinedType.heap]⟩

/-- Valid runtime definitions cannot declare an abstract heap as their unrolled parent. -/
theorem DefinedType.parent_defined {type : DefinedType} {sub : SubType} {parent : HeapType}
    (valid : HeapValid {} type.heap) (unrolled : type.unroll? = some sub)
    (member : parent ∈ sub.supers) : ∃ defined : DefinedType, parent = defined.heap := by
  cases type with
  | mk group index =>
    cases valid with
    | abstract impossible => simp [DefinedType.heap] at impossible
    | defined groupValid bound =>
      cases groupValid with
      | mk entries =>
        simp only [DefinedType.unroll?, RecType.unroll, List.getElem?_map] at unrolled
        obtain ⟨raw, lookup, same⟩ := Option.map_eq_some_iff.mp unrolled
        subst sub
        have rawValid := entries (raw, index)
          (List.mk_mem_zipIdx_iff_getElem?.mpr lookup)
        cases rawValid with
        | mk count values parents =>
          rw [SubType.supers_mapHeap] at member
          obtain ⟨source, belongs, same⟩ := List.mem_map.mp member
          subst parent
          have sourceValid : RuntimeSuperValid {recs := group} index raw.body source := by
            simpa using parents source belongs
          exact sourceValid.unrolled_parent_defined bound

/-- For closed endpoints, the closing-equality case of matching normalizes to identity. -/
theorem DefinedMatches.normalize_closed {ctx : Context} {a b : DefinedType}
    (matched : DefinedMatches ctx a b) (left : a.closed) (right : b.closed) :
    a = b ∨ ∃ sub parent, a.unroll? = some sub ∧ parent ∈ sub.supers ∧
      HeapMatchPath ctx parent b.heap := by
  cases matched.normalize with
  | same ca cb => exact .inl (DefinedType.eq_of_close?_eq left right ca cb)
  | super unrolled member path => exact .inr ⟨_, _, unrolled, member, path⟩

/-- On the runtime domain, a nonidentity defined match starts at a nominal declared parent. -/
theorem DefinedMatches.normalize_runtime {a b : DefinedType}
    (matched : DefinedMatches {} a b) (left : a.closed) (right : b.closed)
    (valid : HeapValid {} a.heap) :
    a = b ∨ ∃ parent : DefinedType, (∃ sub, a.unroll? = some sub ∧ parent.heap ∈ sub.supers) ∧
      HeapMatchPath {} parent.heap b.heap := by
  rcases matched.normalize_closed left right with same | ⟨sub, heap, unrolled, member, path⟩
  · exact .inl same
  · obtain ⟨parent, same⟩ := DefinedType.parent_defined valid unrolled member
    subst heap
    exact .inr ⟨parent, ⟨sub, unrolled, member⟩, path⟩

#print axioms DefinedType.parent_defined
#print axioms DefinedMatches.normalize_runtime

end Wasm.Types
