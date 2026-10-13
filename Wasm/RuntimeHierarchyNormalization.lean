import Wasm.RuntimeNominalTree

/-! Declarative matching preserves runtime hierarchy views, including bottom-type sources. -/
namespace Wasm.Types

def CompType.abstractHeap : CompType → AbstractHeap
  | .func _ => .func
  | .struct_ _ => .struct_
  | .array _ => .array

theorem CompType.abstractHeap_heap (comp : CompType) : comp.abstractHeap.heap = comp.heap := by
  cases comp <;> rfl

private theorem CompType.abstractHeap_eq {a b : CompType} (same : a.heap = b.heap) :
    a.abstractHeap = b.abstractHeap := by
  cases a <;> cases b <;> simp_all [CompType.heap, CompType.abstractHeap]

def HeapType.runtimeView? : HeapType → Option AbstractHeap
  | .func => some .func
  | .nofunc => some .nofunc
  | .extern => some .extern
  | .noextern => some .noextern
  | .exn => some .exn
  | .noexn => some .noexn
  | .bot => some .bot
  | .any => some .any
  | .eq => some .eq
  | .i31 => some .i31
  | .struct_ => some .struct_
  | .array => some .array
  | .none => some .none
  | .defined group index => (DefinedType.mk group index).expandComposite?.map CompType.abstractHeap
  | _ => Option.none

inductive RuntimeHeapView : HeapType → AbstractHeap → Prop where
  | abstract : RuntimeHeapView upper.heap upper
  | defined : RuntimeNominalTree type → type.unroll? = some sub →
      RuntimeHeapView type.heap sub.body.abstractHeap

theorem RuntimeHeapView.computed {heap : HeapType} {upper : AbstractHeap}
    (view : RuntimeHeapView heap upper) : heap.runtimeView? = some upper := by
  cases view with
  | @abstract upper => cases upper <;> rfl
  | defined tree unrolled =>
    simp [DefinedType.heap, HeapType.runtimeView?, DefinedType.expandComposite?, unrolled]

theorem RuntimeHeapView.unique {heap : HeapType} {a b : AbstractHeap}
    (left : RuntimeHeapView heap a) (right : RuntimeHeapView heap b) : a = b :=
  Option.some.inj (left.computed.symm.trans right.computed)

theorem RuntimeHeapView.nominal {type : DefinedType} {upper : AbstractHeap}
    (view : RuntimeHeapView type.heap upper) :
    ∃ sub, RuntimeNominalTree type ∧ type.unroll? = some sub ∧ upper = sub.body.abstractHeap := by
  generalize same : type.heap = heap at view
  cases view with
  | @abstract upper => cases upper <;> simp [AbstractHeap.heap, DefinedType.heap] at same
  | @defined defined sub tree unrolled =>
    have identity : type = defined := by cases type; cases defined; simpa [DefinedType.heap] using same
    subst defined
    exact ⟨sub, tree, unrolled, rfl⟩

theorem RuntimeHeapView.not_bot {heap : HeapType}
    (view : RuntimeHeapView heap .bot) : heap = .bot := by
  generalize same : AbstractHeap.bot = upper at view
  cases view with
  | @abstract upper => cases upper <;> simp_all [AbstractHeap.heap]
  | @defined type sub tree unrolled =>
    cases sub <;> simp [SubType.body, CompType.abstractHeap] at same

theorem RuntimeHeapView.parent {type : DefinedType} {upper : AbstractHeap} {sub : SubType}
    {heap : HeapType} (view : RuntimeHeapView type.heap upper)
    (unrolled : type.unroll? = some sub) (member : heap ∈ sub.supers) :
    RuntimeHeapView heap upper := by
  obtain ⟨actual, tree, found, kind⟩ := view.nominal
  have same := Option.some.inj (found.symm.trans unrolled)
  subst actual
  subst upper
  obtain ⟨parent, same, parentTree, _, parentKind⟩ := tree.parent unrolled member
  subst heap
  obtain ⟨parentSub, parentUnrolled, _⟩ := parentTree.hierarchy
  simp only [DefinedType.hierarchy?, parentUnrolled, Option.map_some, Option.some.injEq] at parentKind
  have kinds := CompType.abstractHeap_eq parentKind
  rw [← kinds]
  exact .defined parentTree parentUnrolled

theorem HeapValid.runtime_view {heap : HeapType} (valid : HeapValid {} heap) :
    ∃ upper, RuntimeHeapView heap upper := by
  cases heap with
  | func => exact ⟨.func, RuntimeHeapView.abstract (upper := .func)⟩
  | nofunc => exact ⟨.nofunc, RuntimeHeapView.abstract (upper := .nofunc)⟩
  | extern => exact ⟨.extern, RuntimeHeapView.abstract (upper := .extern)⟩
  | noextern => exact ⟨.noextern, RuntimeHeapView.abstract (upper := .noextern)⟩
  | exn => exact ⟨.exn, RuntimeHeapView.abstract (upper := .exn)⟩
  | noexn => exact ⟨.noexn, RuntimeHeapView.abstract (upper := .noexn)⟩
  | bot => exact ⟨.bot, RuntimeHeapView.abstract (upper := .bot)⟩
  | any => exact ⟨.any, RuntimeHeapView.abstract (upper := .any)⟩
  | eq => exact ⟨.eq, RuntimeHeapView.abstract (upper := .eq)⟩
  | i31 => exact ⟨.i31, RuntimeHeapView.abstract (upper := .i31)⟩
  | struct_ => exact ⟨.struct_, RuntimeHeapView.abstract (upper := .struct_)⟩
  | array => exact ⟨.array, RuntimeHeapView.abstract (upper := .array)⟩
  | none => exact ⟨.none, RuntimeHeapView.abstract (upper := .none)⟩
  | typeIdx index => cases valid <;> simp_all
  | recIdx index => cases valid <;> simp_all
  | defined group index =>
    have tree := (valid.runtime_nominal_tree rfl).2 ⟨group, index⟩ rfl
    obtain ⟨sub, unrolled, _⟩ := tree.hierarchy
    exact ⟨_, .defined tree unrolled⟩

private theorem source_abstract {heap : HeapType} {a b : AbstractHeap}
    (view : RuntimeHeapView heap a) (same : heap = b.heap) : a = b := by
  subst heap
  exact view.unique .abstract

private theorem view_index_impossible {upper : AbstractHeap} {index : Nat}
    (view : RuntimeHeapView (.typeIdx index) upper) : False := by
  have h := view.computed
  simp [HeapType.runtimeView?] at h

private theorem view_rec_impossible {upper : AbstractHeap} {index : Nat}
    (view : RuntimeHeapView (.recIdx index) upper) : False := by
  have h := view.computed
  simp [HeapType.runtimeView?] at h

private theorem function_view {type : DefinedType} {upper : AbstractHeap} {body : FuncType}
    (view : RuntimeHeapView type.heap upper) (expanded : type.expand? = some body) : upper = .func := by
  obtain ⟨sub, tree, unrolled, rfl⟩ := view.nominal
  cases sub <;> simp_all [DefinedType.expand?, DefinedType.expandComposite?,
    SubType.body, CompType.func?, CompType.abstractHeap]

/-- Matching preserves the finite hierarchy view for all valid runtime endpoints. -/
theorem HeapMatches.runtime_hierarchy {ctx : Context} {a b : HeapType}
    (matched : HeapMatches ctx a b) :
    ctx = {} → ∀ left right, RuntimeHeapView a left → RuntimeHeapView b right →
      left.matches right = true := by
  exact HeapMatches.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun ctx a b _ => ctx = {} → ∀ left right,
      RuntimeHeapView a left → RuntimeHeapView b right → left.matches right = true)
    (motive_7 := fun ctx a b _ => ctx = {} → ∀ left right,
      RuntimeHeapView a.heap left → RuntimeHeapView b.heap right → left.matches right = true)
    (motive_8 := fun _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ left right lv rv => by have same := lv.unique rv; subst right; simp [AbstractHeap.matches])
    (fun valid _ _ _ li ri empty left right lv rv => by
      subst_vars
      obtain ⟨middle, mv⟩ := valid.runtime_view
      exact AbstractHeap.matches_trans (li rfl left middle lv mv) (ri rfl middle right mv rv))
    (fun _ normalized => normalized)
    (fun expanded _ left right lv rv => by
      have ls := function_view lv expanded
      have rs := source_abstract rv (b := .func) rfl
      subst_vars
      rfl)
    (fun _ _ _ _ left right lv _ => False.elim (view_index_impossible lv))
    (fun _ _ _ _ left right _ rv => False.elim (view_index_impossible rv))
    (fun _ _ _ left right lv _ => False.elim (view_rec_impossible lv))
    (fun expanded _ normalized empty left right lv rv => by
      obtain ⟨sub, tree, unrolled, same⟩ := lv.nominal
      simp only [DefinedType.expandComposite?, unrolled, Option.map_some, Option.some.injEq] at expanded
      subst_vars
      apply normalized rfl _ right _ rv
      rw [← CompType.abstractHeap_heap]
      exact .abstract)
    (fun _ _ _ _ left right lv _ => False.elim (view_rec_impossible lv))
    (fun _ left right lv rv => by
      have ls := source_abstract lv (b := .eq) rfl
      have rs := source_abstract rv (b := .any) rfl
      subst_vars
      rfl)
    (fun _ left right lv rv => by
      have ls := source_abstract lv (b := .i31) rfl
      have rs := source_abstract rv (b := .eq) rfl
      subst_vars
      rfl)
    (fun _ left right lv rv => by
      have ls := source_abstract lv (b := .struct_) rfl
      have rs := source_abstract rv (b := .eq) rfl
      subst_vars
      rfl)
    (fun _ left right lv rv => by
      have ls := source_abstract lv (b := .array) rfl
      have rs := source_abstract rv (b := .eq) rfl
      subst_vars
      rfl)
    (fun _ notBottom normalized empty left right lv rv => by
      have ls := source_abstract lv (b := .none) rfl
      subst left
      have h := normalized empty right .any rv (RuntimeHeapView.abstract (upper := .any))
      have notBot : right ≠ .bot := fun same => notBottom (RuntimeHeapView.not_bot (by simpa [same] using rv))
      cases right <;> simp_all [AbstractHeap.matches])
    (fun _ _ _ left right lv _ => False.elim (view_rec_impossible lv))
    (fun _ notBottom normalized empty left right lv rv => by
      have ls := source_abstract lv (b := .nofunc) rfl
      subst left
      have h := normalized empty right .func rv (RuntimeHeapView.abstract (upper := .func))
      have notBot : right ≠ .bot := fun same => notBottom (RuntimeHeapView.not_bot (by simpa [same] using rv))
      cases right <;> simp_all [AbstractHeap.matches])
    (fun _ notBottom normalized empty left right lv rv => by
      have ls := source_abstract lv (b := .noextern) rfl
      subst left
      have h := normalized empty right .extern rv (RuntimeHeapView.abstract (upper := .extern))
      have notBot : right ≠ .bot := fun same => notBottom (RuntimeHeapView.not_bot (by simpa [same] using rv))
      cases right <;> simp_all [AbstractHeap.matches])
    (fun _ notBottom normalized empty left right lv rv => by
      have ls := source_abstract lv (b := .noexn) rfl
      subst left
      have h := normalized empty right .exn rv (RuntimeHeapView.abstract (upper := .exn))
      have notBot : right ≠ .bot := fun same => notBottom (RuntimeHeapView.not_bot (by simpa [same] using rv))
      cases right <;> simp_all [AbstractHeap.matches])
    (fun _ left right lv _ => by
      have ls := source_abstract lv (b := .bot) rfl
      subst left
      cases right <;> rfl)
    (fun ca cb empty left right lv rv => by
      subst_vars
      have same := (DefinedType.eq_of_close_empty ca).trans (DefinedType.eq_of_close_empty cb).symm
      subst_vars
      have same := lv.unique rv
      subst right
      simp [AbstractHeap.matches])
    (fun unrolled member _ normalized empty left right lv rv =>
      normalized empty left right (lv.parent unrolled member) rv)
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
    matched

#print axioms HeapMatches.runtime_hierarchy

end Wasm.Types
