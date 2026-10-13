import Wasm.NominalParentNormalization

/-! A finite declarative certificate for the unrolled nominal-parent graph. -/
namespace Wasm.Types

mutual
  /-- Each node closes to itself and every unrolled parent has a finite nominal certificate. -/
  inductive NominalTree : DefinedType → Prop where
    | mk {type : DefinedType} {sub : SubType} : type.close? [] = some type →
        type.unroll? = some sub →
        (∀ parent ∈ sub.supers, NominalParentTree parent) → NominalTree type

  inductive NominalParentTree : HeapType → Prop where
    | defined : NominalTree type → NominalParentTree type.heap
end

def SubType.ParentsScoped (sub : SubType) (recs : Nat) : Prop :=
  ∀ parent ∈ sub.supers, parent.scoped 0 recs

private theorem parents_scoped {sub : SubType} {fuel recs : Nat}
    (scopeProof : sub.scopedFuel fuel 0 recs = true) : sub.ParentsScoped recs := by
  cases fuel with
  | zero => simp [SubType.scopedFuel] at scopeProof
  | succ fuel =>
    cases sub <;> simp only [SubType.scopedFuel, Bool.and_eq_true] at scopeProof
    case func final supers params results =>
      exact fun parent member => ⟨fuel, List.all_eq_true.mp scopeProof.1.1 parent member⟩
    case struct_ final supers fields =>
      exact fun parent member => ⟨fuel, List.all_eq_true.mp scopeProof.1 parent member⟩
    case array final supers field =>
      exact fun parent member => ⟨fuel, List.all_eq_true.mp scopeProof.1 parent member⟩

private def ParentCertificate (index : Nat) (parent : HeapType) : Prop :=
  (∃ type : DefinedType, parent = type.heap ∧ NominalTree type) ∨
    ∃ earlier, parent = .recIdx earlier ∧ earlier < index

private theorem build_group_tree {group : RecType}
    (parents : ∀ entry ∈ group.zipIdx, ∀ recs, entry.1.ParentsScoped recs →
      ∀ parent ∈ entry.1.supers, ParentCertificate entry.2 parent)
    {fuel : Nat} (scopeProof : group.all (SubType.scopedFuel fuel 0 group.length) = true) :
    ∀ index, index < group.length → NominalTree ⟨group, index⟩ := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
    intro bound
    let type : DefinedType := ⟨group, index⟩
    have closed : type.closed := ⟨fuel + 1, by
      simp [type, DefinedType.heap, HeapType.scopedFuel, bound, scopeProof]⟩
    have lookup : ∃ raw, group[index]? = some raw := by
      exact ⟨group[index], by simp⟩
    obtain ⟨raw, lookup⟩ := lookup
    let sub := raw.mapHeap (.substRecs (unrollIndex group))
    have unrolled : type.unroll? = some sub := by
      simp [type, DefinedType.unroll?, RecType.unroll, List.getElem?_map, lookup, sub]
    apply NominalTree.mk (type.close?_of_closed closed []) unrolled
    intro parent member
    have supers : sub.supers = raw.supers.map (.substRecs (unrollIndex group)) := by
      cases raw <;> rfl
    rw [supers] at member
    obtain ⟨source, belongs, same⟩ := List.mem_map.mp member
    subst parent
    have rawScope := List.all_eq_true.mp scopeProof raw (List.mem_of_getElem? lookup)
    have certificate := parents (raw, index) (List.mk_mem_zipIdx_iff_getElem?.mpr lookup)
      group.length (parents_scoped rawScope) source belongs
    rcases certificate with ⟨defined, same, tree⟩ | ⟨earlier, same, before⟩
    · subst source
      exact .defined tree
    · subst source
      have earlierBound := Nat.lt_trans before bound
      simpa [HeapType.substRecs, unrollIndex, earlierBound, DefinedType.heap] using
        NominalParentTree.defined (ih earlier before earlierBound)

/-- Closed valid runtime definitions have finite nominal-parent trees in every context. -/
theorem HeapValid.nominal_tree {ctx : Context} {heap : HeapType} (valid : HeapValid ctx heap) :
    ∀ type : DefinedType, heap = type.heap → type.closed → NominalTree type := by
  exact HeapValid.rec
    (motive_1 := fun _ heap _ => ∀ type : DefinedType,
      heap = type.heap → type.closed → NominalTree type)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ index sub _ => ∀ recs, sub.ParentsScoped recs →
      ∀ parent ∈ sub.supers, ParentCertificate index parent)
    (motive_4 := fun _ index _ parent _ => ∀ recs,
      parent.scoped 0 recs → ParentCertificate index parent)
    (motive_5 := fun _ group _ => ∀ fuel,
      group.all (SubType.scopedFuel fuel 0 group.length) = true →
      ∀ index, index < group.length → NominalTree ⟨group, index⟩)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ => True)
    (fun abstract type same _ => by
      cases type
      simp [DefinedType.heap] at same
      rw [same] at abstract
      simp at abstract)
    (fun _ type same _ => by cases type; cases same)
    (fun _ type same _ => by cases type; cases same)
    (fun {context group position} _ bound trees type same closed => by
      cases type with
      | mk group position =>
        simp only [DefinedType.heap, HeapType.defined.injEq] at same
        rcases same with ⟨rfl, rfl⟩
        obtain ⟨fuel, scopeProof⟩ := closed
        cases fuel with
        | zero => simp [DefinedType.heap, HeapType.scopedFuel] at scopeProof
        | succ fuel =>
          simp only [DefinedType.heap, HeapType.scopedFuel, Bool.and_eq_true] at scopeProof
          exact trees fuel scopeProof.2 position bound)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ supers recs scopeProof parent member =>
      supers parent member recs (scopeProof parent member))
    (fun {context parent position unfolded body} _ precedes unrolled _ _ heaps _ recs scopeProof => by
      cases parent with
      | typeIdx index =>
        obtain ⟨fuel, checked⟩ := scopeProof
        cases fuel <;> simp [HeapType.scopedFuel] at checked
      | defined group index =>
        have closed : (DefinedType.mk group index).closed := by
          obtain ⟨fuel, checked⟩ := scopeProof
          refine ⟨fuel, ?_⟩
          cases fuel with
          | zero => simp [HeapType.scopedFuel] at checked
          | succ fuel => simpa [DefinedType.heap, HeapType.scopedFuel] using checked
        exact .inl ⟨⟨group, index⟩, rfl, heaps _ rfl closed⟩
      | recIdx earlier => exact .inr ⟨earlier, rfl, precedes⟩
      | _ => simp [HeapType.unrollIn?] at unrolled)
    (fun _ subTrees _ scopeProof => build_group_tree subTrees scopeProof)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    valid

#print axioms HeapValid.nominal_tree

end Wasm.Types
