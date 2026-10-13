import Wasm.MatchingCompleteness

/-! Search completeness for explicit chains of rolled, declared supertypes. -/
namespace Wasm.Types

/-- A declared-parent chain, with successful closing stated independently of search fuel. -/
inductive DefinedSuperPath (ctx : Context) : DefinedType → DefinedType → Nat → Prop where
  | refl : DefinedSuperPath ctx a a 0
  | parent {a b parent left right : DefinedType} {sub : SubType} {length : Nat} :
      a.close? ctx.types = some left → b.close? ctx.types = some right →
      a.unroll? = some sub → parent.heap ∈ sub.supers →
      DefinedSuperPath ctx parent b length → DefinedSuperPath ctx a b (length + 1)

/-- A chain of `length` declared edges is found with `length + 1` units of fuel. -/
theorem DefinedSuperPath.complete {ctx : Context} {a b : DefinedType} {length : Nat}
    (path : DefinedSuperPath ctx a b length) :
    (checkHeap (length + 1) ctx a.heap b.heap).isSome = true := by
  induction path with
  | refl => exact checkHeap_refl _
  | parent closedLeft closedRight unrolled member path ih =>
    exact checkHeap_defined_super_complete closedLeft closedRight unrolled member ih

/-- Declared paths are semantic matches; no structural matching invents nominal edges. -/
theorem DefinedSuperPath.sound {ctx : Context} {a b : DefinedType} {length : Nat}
    (path : DefinedSuperPath ctx a b length) : HeapMatches ctx a.heap b.heap := by
  obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp path.complete
  exact proof.down

#print axioms checkHeap_defined_super_complete
#print axioms DefinedSuperPath.complete
#print axioms DefinedSuperPath.sound

end Wasm.Types
