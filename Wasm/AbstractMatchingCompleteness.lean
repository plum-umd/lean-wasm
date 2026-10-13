import Wasm.MatchingCompleteness

/-!
Normalization and search completeness for the abstract heap hierarchy. The path judgment
allows arbitrary transitivity within this hierarchy; it does not cover paths through defined
or context-indexed types. Every such abstract path is found with two units of search fuel.
-/
namespace Wasm.Types

/-- The finite abstract heap hierarchy, without defined types or context indices. -/
inductive AbstractHeap where
  | func | nofunc | extern | noextern | exn | noexn | bot
  | any | eq | i31 | struct_ | array | none
  deriving DecidableEq, Repr

def AbstractHeap.heap : AbstractHeap → HeapType
  | .func => .func
  | .nofunc => .nofunc
  | .extern => .extern
  | .noextern => .noextern
  | .exn => .exn
  | .noexn => .noexn
  | .bot => .bot
  | .any => .any
  | .eq => .eq
  | .i31 => .i31
  | .struct_ => .struct_
  | .array => .array
  | .none => .none

/-- The normalized reachability table of the abstract hierarchy. -/
def AbstractHeap.matches (a b : AbstractHeap) : Bool :=
  if a = b then true else match a, b with
  | .bot, _ => true
  | .eq, .any | .i31, .eq | .i31, .any | .struct_, .eq | .struct_, .any
    | .array, .eq | .array, .any => true
  | .none, .any | .none, .eq | .none, .i31 | .none, .struct_ | .none, .array => true
  | .nofunc, .func | .noextern, .extern | .noexn, .exn => true
  | _, _ => false

/-- Primitive abstract matching rules, with unrestricted composition inside the hierarchy. -/
inductive AbstractHeapPath : AbstractHeap → AbstractHeap → Prop where
  | refl : AbstractHeapPath a a
  | trans : AbstractHeapPath a middle → AbstractHeapPath middle b → AbstractHeapPath a b
  | eqAny : AbstractHeapPath .eq .any
  | i31Eq : AbstractHeapPath .i31 .eq
  | structEq : AbstractHeapPath .struct_ .eq
  | arrayEq : AbstractHeapPath .array .eq
  | none : AbstractHeapPath a .any → a ≠ .bot → AbstractHeapPath .none a
  | nofunc : AbstractHeapPath a .func → a ≠ .bot → AbstractHeapPath .nofunc a
  | noextern : AbstractHeapPath a .extern → a ≠ .bot → AbstractHeapPath .noextern a
  | noexn : AbstractHeapPath a .exn → a ≠ .bot → AbstractHeapPath .noexn a
  | bot : AbstractHeapPath .bot a

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem AbstractHeap.matches_trans {a middle b : AbstractHeap}
    (left : a.matches middle = true) (right : middle.matches b = true) :
    a.matches b = true := by
  cases a <;> cases middle <;> cases b <;> simp_all [AbstractHeap.matches]

/-- Transitivity and bottom rules normalize to the finite reachability table. -/
theorem AbstractHeapPath.normalize {a b : AbstractHeap} (path : AbstractHeapPath a b) :
    a.matches b = true := by
  induction path with
  | refl => simp [AbstractHeap.matches]
  | trans _ _ left right => exact AbstractHeap.matches_trans left right
  | eqAny | i31Eq | structEq | arrayEq => rfl
  | @none a _ notBottom ih | @nofunc a _ notBottom ih
    | @noextern a _ notBottom ih | @noexn a _ notBottom ih =>
    cases a <;> simp_all [AbstractHeap.matches]
  | @bot target => cases target <;> rfl

/-- The normalized abstract hierarchy is found at every fuel budget of at least two. -/
theorem AbstractHeap.matches_search {a b : AbstractHeap} (matched : a.matches b = true)
    (ctx : Context) (fuel : Nat) :
    (checkHeap (fuel + 2) ctx a.heap b.heap).isSome = true := by
  cases a <;> cases b <;> simp [AbstractHeap.matches] at matched
  all_goals simp [AbstractHeap.heap, checkHeap, searchHeap, Search.toOption, Search.map]

/-- Abstract derivations carry valid intermediate heaps in every context. -/
theorem AbstractHeap.valid (a : AbstractHeap) (ctx : Context) : HeapValid ctx a.heap := by
  apply HeapValid.abstract
  cases a <;> simp [AbstractHeap.heap]

/-- The abstract path fragment embeds into the project's declarative heap matching. -/
theorem AbstractHeapPath.sound {a b : AbstractHeap} (path : AbstractHeapPath a b)
    (ctx : Context) : HeapMatches ctx a.heap b.heap := by
  have success := AbstractHeap.matches_search path.normalize ctx 0
  obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp success
  exact proof.down

/-- Completeness for arbitrary compositions of the abstract matching rules. -/
theorem AbstractHeapPath.complete {a b : AbstractHeap} (path : AbstractHeapPath a b)
    (ctx : Context) (fuel : Nat) :
    (checkHeap (fuel + 2) ctx a.heap b.heap).isSome = true :=
  AbstractHeap.matches_search path.normalize ctx fuel

#print axioms AbstractHeapPath.normalize
#print axioms AbstractHeapPath.complete
#print axioms AbstractHeapPath.sound

end Wasm.Types
