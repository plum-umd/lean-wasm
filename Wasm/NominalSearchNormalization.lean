import Wasm.NominalTree
import Wasm.PositiveHeapNormalization
import Wasm.EmptyClosingNormalization
import Wasm.DeclaredMatchingCompleteness

/-! Declarative matching from closed valid definitions normalizes to searchable nominal paths. -/
namespace Wasm.Types

theorem NominalTree.closing {type : DefinedType} (tree : NominalTree type) :
    type.close? [] = some type := by
  cases tree
  assumption

theorem NominalTree.parent {type : DefinedType} {sub : SubType} {heap : HeapType}
    (tree : NominalTree type) (unrolled : type.unroll? = some sub)
    (member : heap ∈ sub.supers) :
    ∃ parent : DefinedType, heap = parent.heap ∧ NominalTree parent := by
  cases tree with
  | mk closed found parents =>
    have same := Option.some.inj (found.symm.trans unrolled)
    subst sub
    cases parents heap member with
    | defined tree => exact ⟨_, rfl, tree⟩

theorem DefinedSuperPath.append {a middle b : DefinedType} {n m : Nat}
    (left : DefinedSuperPath {} a middle n) (right : DefinedSuperPath {} middle b m)
    (closed : b.close? [] = some b) : DefinedSuperPath {} a b (n + m) := by
  induction left with
  | refl => simpa using right
  | parent ca cb unrolled member path ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      DefinedSuperPath.parent ca closed unrolled member (ih right)

private theorem heap_injective {a b : DefinedType} (same : a.heap = b.heap) : a = b := by
  cases a
  cases b
  simpa [DefinedType.heap] using same

private theorem positive_ne_nominal {upper : AbstractHeap} (positive : upper.Positive)
    (type : DefinedType) : type.heap ≠ upper.heap := by
  cases upper <;> simp_all [AbstractHeap.Positive, AbstractHeap.heap, DefinedType.heap]

private def CompType.upper : CompType → AbstractHeap
  | .func _ => .func
  | .struct_ _ => .struct_
  | .array _ => .array

private theorem CompType.upper_positive (comp : CompType) : comp.upper.Positive := by
  cases comp <;> trivial

private theorem CompType.upper_heap (comp : CompType) : comp.heap = comp.upper.heap := by
  cases comp <;> rfl

private def NominalResult (source : DefinedType) (target : HeapType) : Prop :=
  (∃ defined : DefinedType, ∃ length, target = defined.heap ∧ NominalTree defined ∧
    DefinedSuperPath {} source defined length) ∨
  ∃ upper : AbstractHeap, upper.Positive ∧ target = upper.heap

/-- An arbitrary match from a certified nominal source stays nominal or enters an upper hierarchy. -/
private theorem normalize_nominal {ctx : Context} {a b : HeapType}
    (matched : HeapMatches ctx a b) :
    ∀ source : DefinedType, ctx = {} → NominalTree source → a = source.heap →
      NominalResult source b := by
  exact HeapMatches.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun ctx a b _ => ∀ source : DefinedType,
      ctx = {} → NominalTree source → a = source.heap → NominalResult source b)
    (motive_7 := fun ctx a b _ => ctx = {} → NominalTree a →
      ∃ length, NominalTree b ∧ DefinedSuperPath {} a b length)
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
    (fun source _ tree same => .inl ⟨source, 0, same, tree, .refl⟩)
    (fun _ _ matchedRight _ left right source empty tree same => by
      rcases left source empty tree same with ⟨middle, n, me, mt, pathLeft⟩ | ⟨upper, positive, me⟩
      · rcases right middle empty mt me with ⟨target, m, te, tt, pathRight⟩ | upper
        · exact .inl ⟨target, n + m, te, tt, pathLeft.append pathRight tt.closing⟩
        · exact .inr upper
      · obtain ⟨target, positive, te, _⟩ := matchedRight.normalize_positive upper positive me
        exact .inr ⟨target, positive, te⟩)
    (fun _ normalized source empty tree same => by
      have identity := heap_injective same
      subst source
      obtain ⟨n, target, path⟩ := normalized empty tree
      exact .inl ⟨_, n, rfl, target, path⟩)
    (fun _ _ _ _ _ => .inr ⟨.func, trivial, rfl⟩)
    (fun lookup _ _ source empty _ _ => by subst_vars; simp at lookup)
    (fun lookup _ _ source empty _ _ => by subst_vars; simp at lookup)
    (fun lookup _ source empty _ _ => by subst_vars; simp at lookup)
    (fun {comp context target origin} _ matched _ source empty tree same => by
      obtain ⟨upper, positive, same, _⟩ :=
        matched.normalize_positive comp.upper comp.upper_positive comp.upper_heap
      exact .inr ⟨upper, positive, same⟩)
    (fun lookup _ _ source empty _ _ => by subst_vars; simp at lookup)
    (fun source _ _ same => by cases source; cases same)
    (fun source _ _ same => by cases source; cases same)
    (fun source _ _ same => by cases source; cases same)
    (fun source _ _ same => by cases source; cases same)
    (fun _ _ _ source _ _ same => by cases source; cases same)
    (fun lookup _ source empty _ _ => by subst_vars; simp at lookup)
    (fun _ _ _ source _ _ same => by cases source; cases same)
    (fun _ _ _ source _ _ same => by cases source; cases same)
    (fun _ _ _ source _ _ same => by cases source; cases same)
    (fun source _ _ same => by cases source; cases same)
    (fun ca cb empty tree => by
      subst_vars
      have left := DefinedType.eq_of_close_empty ca
      have right := DefinedType.eq_of_close_empty cb
      have same := left.trans right.symm
      subst_vars
      exact ⟨0, tree, .refl⟩)
    (fun unrolled member _ normalized empty tree => by
      obtain ⟨parent, same, parentTree⟩ := tree.parent unrolled member
      rcases normalized parent empty parentTree same with
        ⟨target, n, sameTarget, targetTree, path⟩ | ⟨upper, positive, sameTarget⟩
      · have identity := heap_injective sameTarget
        subst_vars
        exact ⟨n + 1, targetTree,
          .parent tree.closing targetTree.closing unrolled member path⟩
      · exact False.elim (positive_ne_nominal positive _ sameTarget))
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

/-- All declarative matches between defined runtime types reduce to declared-supertype chains. -/
theorem HeapMatches.normalize_defined_runtime {a b : DefinedType}
    (matched : HeapMatches {} a.heap b.heap) (valid : HeapValid {} a.heap) (closed : a.closed) :
    ∃ length, DefinedSuperPath {} a b length := by
  have tree := valid.nominal_tree a rfl closed
  rcases normalize_nominal matched a rfl tree rfl with
    ⟨target, length, same, _, path⟩ | ⟨upper, positive, same⟩
  · have identity := heap_injective same
    subst target
    exact ⟨length, path⟩
  · exact False.elim (positive_ne_nominal positive b same)

/-- The nominal normalization proof needs only the finite parent-tree certificate. -/
theorem HeapMatches.normalize_defined_tree {a b : DefinedType}
    (matched : HeapMatches {} a.heap b.heap) (tree : NominalTree a) :
    ∃ length, DefinedSuperPath {} a b length := by
  rcases normalize_nominal matched a rfl tree rfl with
    ⟨target, length, same, _, path⟩ | ⟨upper, positive, same⟩
  · have identity := heap_injective same
    subst target
    exact ⟨length, path⟩
  · exact False.elim (positive_ne_nominal positive b same)

/-- A valid closed nominal subtype is found by executable search with sufficient fuel. -/
theorem checkHeap_complete_defined_runtime {a b : DefinedType}
    (matched : HeapMatches {} a.heap b.heap) (valid : HeapValid {} a.heap) (closed : a.closed) :
    ∃ fuel, 0 < fuel ∧ (checkHeap fuel {} a.heap b.heap).isSome = true := by
  obtain ⟨length, path⟩ := matched.normalize_defined_runtime valid closed
  exact ⟨length + 1, Nat.zero_lt_succ _, path.complete⟩

#print axioms HeapMatches.normalize_defined_runtime
#print axioms checkHeap_complete_defined_runtime

end Wasm.Types
