import Wasm.NominalSearchNormalization

/-! Hierarchy coherence and decreasing weights for runtime nominal parent trees. -/
namespace Wasm.Types

mutual
  inductive RuntimeNominalTree : DefinedType → Prop where
    | mk {type : DefinedType} {sub : SubType} : type.close? [] = some type →
        type.unroll? = some sub →
        (∀ parent ∈ sub.supers, RuntimeNominalParent parent) →
        (∀ parent ∈ sub.supers, parent.weight < type.heap.weight) →
        (∀ parent ∈ sub.supers,
          (parent.unrollIn? {}).map (fun sub => sub.body.heap) = some sub.body.heap) →
        RuntimeNominalTree type
  inductive RuntimeNominalParent : HeapType → Prop where
    | defined : RuntimeNominalTree type → RuntimeNominalParent type.heap
end

def DefinedType.hierarchy? (type : DefinedType) : Option HeapType :=
  type.unroll?.map (fun sub => sub.body.heap)

private theorem mapM_fixed {f : α → Option α} {xs : List α}
    (fixed : ∀ x ∈ xs, f x = some x) : xs.mapM f = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, fixed x (by simp), ih (fun x member => fixed x (by simp [member]))]

private theorem field_close_fixed {field : FieldType}
    (fixed : field.storage.unpack.close? [] = some field.storage.unpack) :
    field.close? [] = some field := by
  cases field with
  | mk storage mutable =>
    change storage.unpack.close? [] = some storage.unpack at fixed
    cases storage <;> simp_all [FieldType.close?, StorageType.close?, StorageType.unpack]

private theorem sub_close_fixed {sub : SubType}
    (values : ∀ type ∈ sub.body.valTypes, type.close? [] = some type)
    (parents : ∀ heap ∈ sub.supers, heap.close? [] = some heap) :
    sub.close? [] = some sub := by
  cases sub with
  | func final supers params results =>
    simp only [SubType.supers] at parents
    have hs := mapM_fixed parents
    have hp := mapM_fixed (xs := params) (fun type member => values type (by
      simp [SubType.body, CompType.valTypes, member]))
    have hr := mapM_fixed (xs := results) (fun type member => values type (by
      simp [SubType.body, CompType.valTypes, member]))
    simp [SubType.close?, hs, hp, hr]
  | struct_ final supers fields =>
    simp only [SubType.supers] at parents
    have hs := mapM_fixed parents
    have hf := mapM_fixed (fun field member => field_close_fixed (values field.storage.unpack
      (by simp [SubType.body, CompType.valTypes]; exact ⟨field, member, rfl⟩)))
    simp [SubType.close?, hs, hf]
  | array final supers field =>
    simp only [SubType.supers] at parents
    have hs := mapM_fixed parents
    have hf := field_close_fixed (values field.storage.unpack (by
      simp [SubType.body, CompType.valTypes]))
    simp [SubType.close?, hs, hf]

private theorem fold_add_acc (xs : List Nat) (n : Nat) :
    xs.foldl (· + ·) n = n + xs.foldl (· + ·) 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (n + x), ih x]
    omega

private theorem member_le_total {xs : List α} {x : α} (f : α → Nat) (member : x ∈ xs) :
    f x ≤ (xs.map f).foldl (· + ·) 0 := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rw [fold_add_acc]
    rcases List.mem_cons.mp member with same | member
    · subst x; omega
    · have h := ih member; omega

private theorem parent_weight_lt_sub {sub : SubType} {parent : HeapType}
    (member : parent ∈ sub.supers) : parent.weight < sub.weight := by
  have bound := member_le_total HeapType.weight member
  cases sub <;> simp only [SubType.supers, SubType.weight] at bound ⊢ <;> omega

private theorem body_heap_map (sub : SubType) (f : HeapType → HeapType) :
    (sub.mapHeap f).body.heap = sub.body.heap := by
  cases sub <;> rfl

private theorem supers_map (sub : SubType) (f : HeapType → HeapType) :
    (sub.mapHeap f).supers = sub.supers.map f := by
  cases sub <;> rfl

private theorem CompMatches.hierarchy (matched : CompMatches ctx a b) : a.heap = b.heap := by
  cases matched <;> rfl

private def ParentCertificate (ctx : Context) (index : Nat) (kind : HeapType)
    (parent : HeapType) : Prop :=
  (∃ type : DefinedType, parent = type.heap ∧ RuntimeNominalTree type ∧
    type.hierarchy? = some kind) ∨
  ∃ earlier sub, parent = .recIdx earlier ∧ earlier < index ∧
    ctx.recs[earlier]? = some sub ∧ sub.body.heap = kind

private theorem build_runtime_group {ctx : Context} {group : RecType}
    (closing : group.mapM (SubType.close? []) = some group)
    (certificates : ∀ entry ∈ group.zipIdx, ∀ parent ∈ entry.1.supers,
      ParentCertificate ctx entry.2 entry.1.body.heap parent)
    {rest : RecType} (contextRecs : ctx.recs = group ++ rest) :
    ∀ index, index < group.length → RuntimeNominalTree ⟨group, index⟩ := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
    intro bound
    obtain ⟨raw, lookup⟩ : ∃ raw, group[index]? = some raw := ⟨group[index], by simp⟩
    let type : DefinedType := ⟨group, index⟩
    let sub := raw.mapHeap (.substRecs (unrollIndex group))
    have unrolled : type.unroll? = some sub := by
      simp [type, DefinedType.unroll?, RecType.unroll, List.getElem?_map, lookup, sub]
    have cert : ∀ parent ∈ sub.supers,
        RuntimeNominalParent parent ∧ parent.weight < type.heap.weight ∧
          (parent.unrollIn? {}).map (fun sub => sub.body.heap) = some sub.body.heap := by
      intro parent member
      rw [supers_map] at member
      obtain ⟨source, belongs, same⟩ := List.mem_map.mp member
      subst parent
      have certificate := certificates (raw, index)
        (List.mk_mem_zipIdx_iff_getElem?.mpr lookup) source belongs
      rcases certificate with ⟨defined, same, tree, kind⟩ |
        ⟨earlier, ancestor, same, before, ancestorLookup, kind⟩
      · subst source
        have pw := parent_weight_lt_sub belongs
        simp only [DefinedType.heap, HeapType.weight] at pw
        have rw := member_le_total SubType.weight (List.mem_of_getElem? lookup)
        refine ⟨.defined tree, ?_, ?_⟩
        · simp only [type, DefinedType.heap, HeapType.substRecs, HeapType.weight]
          omega
        · simp only [DefinedType.heap, HeapType.substRecs, HeapType.unrollIn?, sub,
            body_heap_map]
          exact kind
      · subst source
        have earlierBound := Nat.lt_trans before bound
        have ancestorLookup' : group[earlier]? = some ancestor := by
          simpa [contextRecs, List.getElem?_append, earlierBound] using ancestorLookup
        have earlierUnrolled : (DefinedType.mk group earlier).unroll? =
            some (ancestor.mapHeap (.substRecs (unrollIndex group))) := by
          simp [DefinedType.unroll?, RecType.unroll, List.getElem?_map, ancestorLookup']
        refine ⟨?_, ?_, ?_⟩
        · simpa [HeapType.substRecs, unrollIndex, earlierBound, DefinedType.heap] using
            RuntimeNominalParent.defined (ih earlier before earlierBound)
        · simp [HeapType.substRecs, unrollIndex, earlierBound, DefinedType.heap,
            HeapType.weight, type]
          omega
        · simp [HeapType.substRecs, unrollIndex, earlierBound, HeapType.unrollIn?,
            earlierUnrolled, body_heap_map, kind, sub]
    apply RuntimeNominalTree.mk (by simp [DefinedType.close?, closing, type]) unrolled
    · exact fun parent member => (cert parent member).1
    · exact fun parent member => (cert parent member).2.1
    · exact fun parent member => (cert parent member).2.2

/-- Valid types in a runtime context close to themselves and have coherent weighted parent trees. -/
theorem HeapValid.runtime_nominal_tree {ctx : Context} {heap : HeapType}
    (valid : HeapValid ctx heap) : ctx.types = [] →
    heap.close? [] = some heap ∧
      ∀ type : DefinedType, heap = type.heap → RuntimeNominalTree type := by
  exact HeapValid.rec
    (motive_1 := fun ctx heap _ => ctx.types = [] → heap.close? [] = some heap ∧
      ∀ type : DefinedType, heap = type.heap → RuntimeNominalTree type)
    (motive_2 := fun ctx type _ => ctx.types = [] → type.close? [] = some type)
    (motive_3 := fun ctx index sub _ => ctx.types = [] → sub.close? [] = some sub ∧
      ∀ parent ∈ sub.supers, ParentCertificate ctx index sub.body.heap parent)
    (motive_4 := fun ctx index body parent _ => ctx.types = [] →
      parent.close? [] = some parent ∧ ParentCertificate ctx index body.heap parent)
    (motive_5 := fun ctx group _ => ctx.types = [] → ∀ rest, ctx.recs = group ++ rest →
      group.mapM (SubType.close? []) = some group ∧
        ∀ index, index < group.length → RuntimeNominalTree ⟨group, index⟩)
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
    (fun {heap context} abstract empty => by
      refine ⟨?_, ?_⟩
      · cases heap <;> simp_all [HeapType.close?]
      · intro type same; cases type; rw [same] at abstract; simp [DefinedType.heap] at abstract)
    (fun lookup empty => by simp [empty] at lookup)
    (fun _ _ => ⟨by simp [HeapType.close?], by intro type same; cases type; cases same⟩)
    (fun {context group position} _ bound trees empty => by
      obtain ⟨closing, certified⟩ := trees empty context.recs rfl
      refine ⟨by simp [HeapType.close?, closing], ?_⟩
      intro type same
      cases type with
      | mk group position =>
        simp only [DefinedType.heap, HeapType.defined.injEq] at same
        rcases same with ⟨rfl, rfl⟩
        exact certified _ bound)
    (fun {type context} number _ => by cases type <;> simp_all [ValType.close?])
    (fun _ heaps empty => by simp [ValType.close?, (heaps empty).1])
    (fun _ _ _ values parents empty => by
      refine ⟨sub_close_fixed (fun type member => values type member empty)
        (fun parent member => (parents parent member empty).1), ?_⟩
      exact fun parent member => (parents parent member empty).2)
    (fun {context parent position unfolded body} _ prior unrolled _ matched heaps _ empty => by
      have heapInfo := heaps empty
      refine ⟨heapInfo.1, ?_⟩
      have compatible := CompMatches.hierarchy matched
      cases parent with
      | defined group index =>
        refine .inl ⟨⟨group, index⟩, rfl, heapInfo.2 _ rfl, ?_⟩
        change (DefinedType.mk group index).unroll? = some unfolded at unrolled
        simp only [DefinedType.hierarchy?, unrolled, Option.map_some]
        exact congrArg some compatible.symm
      | recIdx earlier =>
        exact .inr ⟨earlier, unfolded, rfl, prior, unrolled, compatible.symm⟩
      | typeIdx index => simp [HeapType.unrollIn?, empty] at unrolled
      | _ => simp [HeapType.unrollIn?] at unrolled)
    (fun {context group} _ subs empty rest contextRecs => by
      have closing := mapM_fixed (fun sub member => by
        obtain ⟨index, lookup⟩ := List.getElem?_of_mem member
        exact (subs (sub, index) (List.mk_mem_zipIdx_iff_getElem?.mpr lookup) empty).1)
      refine ⟨closing, ?_⟩
      exact build_runtime_group closing
        (by
          intro entry member parent belongs
          exact (subs entry member empty).2 parent belongs) contextRecs)
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

theorem RuntimeNominalTree.nominal {type : DefinedType} (tree : RuntimeNominalTree type) :
    NominalTree type :=
  RuntimeNominalTree.rec
    (motive_1 := fun type _ => NominalTree type)
    (motive_2 := fun heap _ => NominalParentTree heap)
    (fun closing unrolled _ _ _ trees => .mk closing unrolled trees)
    (fun _ tree => .defined tree) tree

theorem RuntimeNominalTree.closing {type : DefinedType} (tree : RuntimeNominalTree type) :
    type.close? [] = some type := tree.nominal.closing

theorem RuntimeNominalTree.parent {type : DefinedType} {sub : SubType} {heap : HeapType}
    (tree : RuntimeNominalTree type) (unrolled : type.unroll? = some sub)
    (member : heap ∈ sub.supers) :
    ∃ parent : DefinedType, heap = parent.heap ∧ RuntimeNominalTree parent ∧
      parent.heap.weight < type.heap.weight ∧ parent.hierarchy? = some sub.body.heap := by
  cases tree with
  | mk closed found parents smaller kinds =>
    have same := Option.some.inj (found.symm.trans unrolled)
    subst sub
    have size := smaller heap member
    have kind := kinds heap member
    cases parents heap member with
    | defined tree => exact ⟨_, rfl, tree, size, kind⟩

theorem RuntimeNominalTree.hierarchy {type : DefinedType} (tree : RuntimeNominalTree type) :
    ∃ sub, type.unroll? = some sub ∧ type.hierarchy? = some sub.body.heap := by
  cases tree with
  | mk closing unrolled _ _ _ =>
    exact ⟨_, unrolled, by simp [DefinedType.hierarchy?, unrolled]⟩

private theorem defined_heap_injective {a b : DefinedType} (same : a.heap = b.heap) : a = b := by
  cases a
  cases b
  simpa [DefinedType.heap] using same

/-- Valid declared-parent chains have length bounded by the source's existing syntax weight. -/
theorem DefinedSuperPath.length_le_weight {a b : DefinedType} {length : Nat}
    (path : DefinedSuperPath {} a b length) (tree : RuntimeNominalTree a) :
    length ≤ a.heap.weight := by
  induction path with
  | refl => omega
  | parent ca cb unrolled member path ih =>
    obtain ⟨parent, same, parentTree, smaller, _⟩ := tree.parent unrolled member
    have identity := defined_heap_injective same
    cases identity
    have bound := ih parentTree
    omega

/-- A declared chain succeeds at every budget above its length. -/
theorem DefinedSuperPath.complete_at {a b : DefinedType} {length fuel : Nat}
    (path : DefinedSuperPath {} a b length) (enough : length + 1 ≤ fuel) :
    (checkHeap fuel {} a.heap b.heap).isSome = true := by
  induction path generalizing fuel with
  | refl =>
    cases fuel with
    | zero => omega
    | succ fuel => exact checkHeap_refl _
  | parent ca cb unrolled member path ih =>
    cases fuel with
    | zero => omega
    | succ fuel => exact checkHeap_defined_super_complete ca cb unrolled member (ih (by omega))

#print axioms HeapValid.runtime_nominal_tree

end Wasm.Types
