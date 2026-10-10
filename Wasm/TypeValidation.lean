import Wasm.TypeMatching

/-! Source recursive function type validity and sequential type-section resolution.
https://webassembly.github.io/spec/core/valid/types.html -/
namespace Wasm.Types

def ValType.Valid (ctx : Context) : ValType → Prop
  | .ref _ heap => heap.scoped ctx.types.length ctx.recs.length
  | _ => True

structure SubType.Valid (ctx : Context) (index : Nat) (sub : SubType) : Prop where
  source : sub.isSource = true
  atMostOneSuper : sub.supers.length ≤ 1
  params : ∀ type ∈ sub.body.params, type.Valid ctx
  results : ∀ type ∈ sub.body.results, type.Valid ctx
  supers : ∀ parent ∈ sub.supers, ∃ x defined unfolded,
    parent = .typeIdx x ∧ x < index ∧ ctx.types[x]? = some defined ∧
    defined.unroll? = some unfolded ∧ unfolded.isFinal = false ∧
    FuncMatches ctx sub.body unfolded.body

def RecType.Valid (ctx : Context) (base : Nat) (group : RecType) : Prop :=
  ∀ (i : Nat) (sub : SubType), group[i]? = some sub → sub.Valid ctx (base + i)

/-- Resolve a group against earlier groups after rolling its locally bound indices. -/
def RecType.resolve? (previous : List DefinedType) (group : RecType) :
    Option (List DefinedType) := do
  let closed ← (group.roll previous.length).mapM (SubType.close? previous)
  return RecType.projections closed

def resolveSection? : List DefinedType → List RecType → Option (List DefinedType)
  | previous, [] => some previous
  | previous, group :: rest => do
    let resolved ← group.resolve? previous
    resolveSection? (previous ++ resolved) rest

/-- Validation is declarative: resolution alone does not certify subtype declarations. -/
inductive TypeSectionValid : List DefinedType → List RecType → List DefinedType → Prop where
  | nil : TypeSectionValid previous [] previous
  | cons : group.resolve? previous = some resolved →
      (∀ type ∈ resolved, type.closed) →
      group.Valid ⟨previous ++ resolved, []⟩ previous.length →
      TypeSectionValid (previous ++ resolved) rest final →
      TypeSectionValid previous (group :: rest) final

end Wasm.Types
