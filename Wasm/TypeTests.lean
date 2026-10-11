import Wasm.TypeEmbedding

set_option linter.unusedSimpArgs false

namespace Wasm.Types.Tests

private def recursiveAt (base : Nat) : RecType :=
  [.func true [] [.ref true (.typeIdx base)] [.ref false (.typeIdx (base + 1))],
   .func true [] [.ref true (.typeIdx (base + 1))] []]

-- The same group has identical identity at different module offsets.
example : (recursiveAt 0).roll 0 = (recursiveAt 7).roll 7 := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

example : ((recursiveAt 0).roll 0).resolve? [] ≠ none := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

example : RecType.resolve? [] [.func true [] [.ref true (.typeIdx 1)] []] = none := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

-- A nested defined type binds its own recursion indices.
example : (HeapType.defined [.func true [] [.ref true (.recIdx 0)] []] 0).substRecs
    (fun _ => .extern) = .defined [.func true [] [.ref true (.recIdx 0)] []] 0 := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

example : HeapType.scopedFuel 20 0 0
    (.defined [.func true [] [.ref true (.recIdx 0)] []] 0) = true := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]
example : HeapType.scopedFuel 20 0 0 (.recIdx 0) = false := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]
example : HeapType.scopedFuel 20 0 0 (.defined [] 0) = false := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

example : RefMatches {} ⟨false, .nofunc⟩ ⟨true, .func⟩ :=
  ⟨(by intro h; cases h), .nofunc .refl (by intro h; cases h)⟩
example : RefMatches {} ⟨true, .noextern⟩ ⟨true, .extern⟩ :=
  ⟨id, .noextern .refl (by intro h; cases h)⟩
example : ¬ RefMatches {} ⟨true, .func⟩ ⟨false, .func⟩ := nullable_not_nonNull {} _ _

-- Accept a broader parameter and return a narrower result.
private theorem narrowRef : RefMatches {} ⟨false, .nofunc⟩ ⟨true, .func⟩ :=
  ⟨(by simp), .nofunc .refl (by intro h; cases h)⟩

example : FuncMatches {}
    ⟨[.ref true .func], [.ref false .nofunc]⟩
    ⟨[.ref false .nofunc], [.ref true .func]⟩ :=
  ⟨.cons (.ref narrowRef) .nil, .cons (.ref narrowRef) .nil⟩

example : (.ref false (.typeIdx 0) : ValType).defaultable = false := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]
example : (RefType.difference ⟨true, .func⟩ ⟨false, .nofunc⟩).nullable = true := by
  simp [recursiveAt, RecType.roll, SubType.substTypes, ValType.substTypes,
    HeapType.substTypes, rollIndex, RecType.resolve?, SubType.close?, ValType.close?,
    HeapType.close?, RecType.projections, HeapType.scopedFuel, SubType.scopedFuel,
    ValType.scopedFuel, HeapType.substRecs, ValType.defaultable, RefType.difference]

example : SubType.Valid ⟨[⟨[.func true [] [] []], 0⟩], []⟩ 0
    (.func true [] [] []) := by
  constructor
  · rfl
  · decide
  · simp [SubType.body, CompType.valTypes]
  · simp [SubType.supers]

-- A parent must precede its child, even inside the same recursive group.
example (ctx : Context) : ¬ SubType.Valid ctx 0 (.func false [.typeIdx 0] [] []) := by
  intro h
  obtain ⟨x, defined, unfolded, heq, hlt, _⟩ :=
    h.supers (.typeIdx 0) (by simp [SubType.supers])
  cases heq
  omega

-- Declaring a subtype of a final function is rejected.
example : ¬ SubType.Valid ⟨[⟨[.func true [] [] []], 0⟩], []⟩ 1
    (.func true [.typeIdx 0] [] []) := by
  intro h
  obtain ⟨x, defined, unfolded, heq, _, lookup, expanded, nonfinal, _⟩ :=
    h.supers (.typeIdx 0) (by simp [SubType.supers])
  cases heq
  simp at lookup
  subst defined
  simp [DefinedType.unroll?, RecType.unroll, SubType.mapHeap] at expanded
  subst unfolded
  contradiction

#print axioms Wasm.Types.embedVal_injective
#print axioms Wasm.Types.RefMatches.trans

end Wasm.Types.Tests
