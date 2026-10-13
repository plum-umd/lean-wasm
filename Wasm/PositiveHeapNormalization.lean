import Wasm.AbstractMatchingCompleteness

/-! Positive abstract heap types cannot return to nominal types or hierarchy bottoms. -/
namespace Wasm.Types

/-- Abstract upper types, excluding validation and hierarchy bottoms. -/
def AbstractHeap.Positive : AbstractHeap → Prop
  | .func | .extern | .exn | .any | .eq | .i31 | .struct_ | .array => True
  | _ => False

private theorem positive_ne_defined (source : AbstractHeap) (positive : source.Positive)
    (type : DefinedType) : type.heap ≠ source.heap := by
  cases source <;> simp_all [AbstractHeap.Positive, AbstractHeap.heap, DefinedType.heap]

/-- A match from an abstract upper type stays in the finite abstract upper hierarchy. -/
theorem HeapMatches.normalize_positive {ctx : Context} {a b : HeapType}
    (matched : HeapMatches ctx a b) :
    ∀ source : AbstractHeap, source.Positive → a = source.heap →
      ∃ target : AbstractHeap, target.Positive ∧ b = target.heap ∧ source.matches target = true := by
  exact HeapMatches.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun _ a b _ => ∀ source : AbstractHeap, source.Positive → a = source.heap →
      ∃ target : AbstractHeap, target.Positive ∧ b = target.heap ∧ source.matches target = true)
    (motive_7 := fun _ _ _ _ => True)
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
    (fun source positive same => ⟨source, positive, same, by simp [AbstractHeap.matches]⟩)
    (fun _ _ _ _ left right source positive same => by
      obtain ⟨middle, mp, me, lm⟩ := left source positive same
      obtain ⟨target, tp, te, rm⟩ := right middle mp me
      exact ⟨target, tp, te, AbstractHeap.matches_trans lm rm⟩)
    (fun _ _ source positive same => False.elim (positive_ne_defined source positive _ same))
    (fun _ source positive same => False.elim (positive_ne_defined source positive _ same))
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ normalized source positive same => by
      obtain ⟨target, tp, te, _⟩ := normalized source positive same
      exact False.elim (positive_ne_defined target tp _ te))
    (fun _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ _ source positive same => False.elim (positive_ne_defined source positive _ same))
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same
      exact ⟨.any, trivial, rfl, rfl⟩)
    (fun source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same
      exact ⟨.eq, trivial, rfl, rfl⟩)
    (fun source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same
      exact ⟨.eq, trivial, rfl, rfl⟩)
    (fun source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same
      exact ⟨.eq, trivial, rfl, rfl⟩)
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun _ _ _ source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
    (fun source positive same => by
      cases source <;> simp [AbstractHeap.Positive, AbstractHeap.heap] at positive same)
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
    matched

/-- Abstract upper-type matches never end at a defined type, in any context. -/
theorem HeapMatches.positive_not_defined {ctx : Context} {source : AbstractHeap}
    (positive : source.Positive) (type : DefinedType) : ¬ HeapMatches ctx source.heap type.heap := by
  intro matched
  obtain ⟨target, tp, same, _⟩ := matched.normalize_positive source positive rfl
  exact positive_ne_defined target tp type same

/-- General declarative matches from abstract upper types are found with two units of fuel. -/
theorem checkHeap_complete_positive {ctx : Context} {source : AbstractHeap} {target : HeapType}
    (positive : source.Positive) (matched : HeapMatches ctx source.heap target) (fuel : Nat) :
    (checkHeap (fuel + 2) ctx source.heap target).isSome = true := by
  obtain ⟨upper, _, same, normalized⟩ := matched.normalize_positive source positive rfl
  subst target
  exact AbstractHeap.matches_search normalized ctx fuel

#print axioms HeapMatches.normalize_positive
#print axioms HeapMatches.positive_not_defined
#print axioms checkHeap_complete_positive

end Wasm.Types
