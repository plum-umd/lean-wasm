import Wasm.TypeSyntax

/-! Function/external type matching, following the Wasm 3.0 matching rules.
https://webassembly.github.io/spec/core/valid/matching.html -/
namespace Wasm.Types

structure Context where
  types : List DefinedType := []
  recs : RecType := []

mutual
  inductive HeapMatches (ctx : Context) : HeapType → HeapType → Prop where
    | refl : HeapMatches ctx a a
    | trans : middle.scoped ctx.types.length ctx.recs.length →
        HeapMatches ctx a middle → HeapMatches ctx middle b → HeapMatches ctx a b
    | defined : DefinedMatches ctx a b → HeapMatches ctx a.heap b.heap
    | definedFunc {a : DefinedType} {body : FuncType} : a.expand? = some body → HeapMatches ctx a.heap .func
    | indexLeft : ctx.types[x]? = some a → HeapMatches ctx a.heap b →
        HeapMatches ctx (.typeIdx x) b
    | indexRight : ctx.types[x]? = some b → HeapMatches ctx a b.heap →
        HeapMatches ctx a (.typeIdx x)
    | recFunc : ctx.recs[i]? = some sub → HeapMatches ctx (.recIdx i) .func
    | recSuper : ctx.recs[i]? = some sub → parent ∈ sub.supers →
        HeapMatches ctx (.recIdx i) parent
    | nofunc : HeapMatches ctx a .func → a ≠ .bot → HeapMatches ctx .nofunc a
    | noextern : HeapMatches ctx a .extern → a ≠ .bot → HeapMatches ctx .noextern a
    | bot : HeapMatches ctx .bot a

  /-- Identity is equality after closing; structural variance alone does not declare a subtype. -/
  inductive DefinedMatches (ctx : Context) : DefinedType → DefinedType → Prop where
    | same : a.close? ctx.types = some closed → b.close? ctx.types = some closed →
        DefinedMatches ctx a b
    | super : a.unroll? = some sub → parent ∈ sub.supers →
        HeapMatches ctx parent b.heap → DefinedMatches ctx a b
end

structure RefMatches (ctx : Context) (a b : RefType) : Prop where
  nullability : a.nullable = true → b.nullable = true
  heap : HeapMatches ctx a.heap b.heap

inductive ValMatches (ctx : Context) : ValType → ValType → Prop where
  | i32 : ValMatches ctx .i32 .i32
  | i64 : ValMatches ctx .i64 .i64
  | f32 : ValMatches ctx .f32 .f32
  | f64 : ValMatches ctx .f64 .f64
  | ref : RefMatches ctx a b → ValMatches ctx a.val b.val
  | bot : ValMatches ctx .bot a

inductive ResultMatches (ctx : Context) : List ValType → List ValType → Prop where
  | nil : ResultMatches ctx [] []
  | cons : ValMatches ctx a b → ResultMatches ctx as bs →
      ResultMatches ctx (a :: as) (b :: bs)

/-- Function parameters are contravariant; results are covariant. -/
structure FuncMatches (ctx : Context) (a b : FuncType) : Prop where
  params : ResultMatches ctx b.params a.params
  results : ResultMatches ctx a.results b.results

theorem RefMatches.refl (ctx : Context) (a : RefType) : RefMatches ctx a a :=
  ⟨id, .refl⟩

theorem RefMatches.trans (ab : RefMatches ctx a b) (bc : RefMatches ctx b c)
    (valid : b.heap.scoped ctx.types.length ctx.recs.length) : RefMatches ctx a c :=
  ⟨fun h => bc.nullability (ab.nullability h), .trans valid ab.heap bc.heap⟩

theorem nonNull_matches_nullable (ctx : Context) (heap : HeapType) :
    RefMatches ctx ⟨false, heap⟩ ⟨true, heap⟩ := ⟨by simp, .refl⟩

theorem nullable_not_nonNull (ctx : Context) (a b : HeapType) :
    ¬ RefMatches ctx ⟨true, a⟩ ⟨false, b⟩ := by
  intro h
  have := h.nullability rfl
  contradiction

end Wasm.Types
