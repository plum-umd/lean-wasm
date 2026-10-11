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
    | definedFunc {a : DefinedType} {body : FuncType} :
        a.expand? = some body → HeapMatches ctx a.heap .func
    | indexLeft : ctx.types[x]? = some a → HeapMatches ctx a.heap b →
        HeapMatches ctx (.typeIdx x) b
    | indexRight : ctx.types[x]? = some b → HeapMatches ctx a b.heap →
        HeapMatches ctx a (.typeIdx x)
    | recFunc : ctx.recs[i]? = some sub → sub.body = .func ft →
        HeapMatches ctx (.recIdx i) .func
    | definedComp {a : DefinedType} : a.expandComposite? = some comp →
        HeapMatches ctx comp.heap b → HeapMatches ctx a.heap b
    | recComp : ctx.recs[i]? = some sub → HeapMatches ctx sub.body.heap b →
        HeapMatches ctx (.recIdx i) b
    | eqAny : HeapMatches ctx .eq .any
    | i31Eq : HeapMatches ctx .i31 .eq
    | structEq : HeapMatches ctx .struct_ .eq
    | arrayEq : HeapMatches ctx .array .eq
    | none : HeapMatches ctx a .any → a ≠ .bot → HeapMatches ctx .none a
    | recSuper : ctx.recs[i]? = some sub → parent ∈ sub.supers →
        HeapMatches ctx (.recIdx i) parent
    | nofunc : HeapMatches ctx a .func → a ≠ .bot → HeapMatches ctx .nofunc a
    | noextern : HeapMatches ctx a .extern → a ≠ .bot → HeapMatches ctx .noextern a
    | noexn : HeapMatches ctx a .exn → a ≠ .bot → HeapMatches ctx .noexn a
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
  | v128 : ValMatches ctx .v128 .v128
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

inductive StorageMatches (ctx : Context) : StorageType → StorageType → Prop where
  | val : ValMatches ctx a b → StorageMatches ctx (.val a) (.val b)
  | i8 : StorageMatches ctx .i8 .i8
  | i16 : StorageMatches ctx .i16 .i16

structure FieldMatches (ctx : Context) (a b : FieldType) : Prop where
  mutable : a.mutable = b.mutable
  covariant : StorageMatches ctx a.storage b.storage
  invariant : a.mutable = true → StorageMatches ctx b.storage a.storage

inductive FieldsMatches (ctx : Context) : List FieldType → List FieldType → Prop where
  | nil : FieldsMatches ctx fields []
  | cons : FieldMatches ctx a b → FieldsMatches ctx as bs →
      FieldsMatches ctx (a :: as) (b :: bs)

inductive CompMatches (ctx : Context) : CompType → CompType → Prop where
  | func : FuncMatches ctx a b → CompMatches ctx (.func a) (.func b)
  | struct_ : FieldsMatches ctx as bs → CompMatches ctx (.struct_ as) (.struct_ bs)
  | array : FieldMatches ctx a b → CompMatches ctx (.array a) (.array b)

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
