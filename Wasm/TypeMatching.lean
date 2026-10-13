import Wasm.TypeSyntax

/-! Function/external type matching, following the Wasm 3.0 matching rules.
https://webassembly.github.io/spec/core/valid/matching.html -/
namespace Wasm.Types

structure Context where
  types : List DefinedType := []
  recs : RecType := []

/-- Unroll a type use in the extended runtime context. -/
def HeapType.unrollIn? (ctx : Context) : HeapType → Option SubType
  | .defined group index => (DefinedType.mk group index).unroll?
  | .typeIdx index => ctx.types[index]?.bind DefinedType.unroll?
  | .recIdx index => ctx.recs[index]?
  | _ => Option.none

/-- Recursive parents must precede the current subtype in its group. -/
def HeapType.Precedes (parent : HeapType) (index : Nat) : Prop :=
  match parent with
  | .recIdx i => i < index
  | _ => True

-- Runtime validity checks parent compatibility, whose matching derivations in turn
-- require valid intermediate heaps. Define the judgments together.
mutual
  /-- Runtime heap validity, including validity of rolled recursive declarations.
  https://webassembly.github.io/spec/core/appendix/properties.html#valid-deftype -/
  inductive HeapValid : Context → HeapType → Prop where
    | abstract : heap ∈ [HeapType.func, .nofunc, .extern, .noextern, .exn, .noexn,
        .bot, .any, .eq, .i31, .struct_, .array, .none] → HeapValid ctx heap
    | index : ctx.types[i]? = some type → HeapValid ctx (.typeIdx i)
    | recIndex : ctx.recs[i]? = some sub → HeapValid ctx (.recIdx i)
    | defined : RuntimeRecValid {ctx with recs := group ++ ctx.recs} group →
        i < group.length → HeapValid ctx (.defined group i)

  inductive RuntimeValValid : Context → ValType → Prop where
    | number : type ∈ [ValType.i32, .i64, .f32, .f64, .v128, .bot] →
        RuntimeValValid ctx type
    | ref : HeapValid ctx heap → RuntimeValValid ctx (.ref nullable heap)

  inductive RuntimeSubValid : Context → Nat → SubType → Prop where
    | mk : sub.supers.length ≤ 1 →
        (∀ type ∈ sub.body.valTypes, RuntimeValValid ctx type) →
        (∀ parent ∈ sub.supers, RuntimeSuperValid ctx index sub.body parent) →
        RuntimeSubValid ctx index sub

  inductive RuntimeSuperValid : Context → Nat → CompType → HeapType → Prop where
    | mk : HeapValid ctx parent → parent.Precedes index →
        parent.unrollIn? ctx = some unfolded → unfolded.isFinal = false →
        CompMatches ctx body unfolded.body → RuntimeSuperValid ctx index body parent

  inductive RuntimeRecValid : Context → RecType → Prop where
    | mk : (∀ entry ∈ group.zipIdx, RuntimeSubValid ctx entry.2 entry.1) →
        RuntimeRecValid ctx group

  inductive HeapMatches : Context → HeapType → HeapType → Prop where
    | refl : HeapMatches ctx a a
    | trans : HeapValid ctx middle →
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
  inductive DefinedMatches : Context → DefinedType → DefinedType → Prop where
    | same : a.close? ctx.types = some closed → b.close? ctx.types = some closed →
        DefinedMatches ctx a b
    | super : a.unroll? = some sub → parent ∈ sub.supers →
        HeapMatches ctx parent b.heap → DefinedMatches ctx a b

  inductive RefMatches : Context → RefType → RefType → Prop where
    | mk : (a.nullable = true → b.nullable = true) → HeapMatches ctx a.heap b.heap →
        RefMatches ctx a b

  inductive ValMatches : Context → ValType → ValType → Prop where
    | i32 : ValMatches ctx .i32 .i32
    | i64 : ValMatches ctx .i64 .i64
    | f32 : ValMatches ctx .f32 .f32
    | f64 : ValMatches ctx .f64 .f64
    | v128 : ValMatches ctx .v128 .v128
    | ref : RefMatches ctx a b → ValMatches ctx a.val b.val
    | bot : ValMatches ctx .bot a

  inductive ResultMatches : Context → List ValType → List ValType → Prop where
    | nil : ResultMatches ctx [] []
    | cons : ValMatches ctx a b → ResultMatches ctx as bs →
        ResultMatches ctx (a :: as) (b :: bs)

  /-- Function parameters are contravariant; results are covariant. -/
  inductive FuncMatches : Context → FuncType → FuncType → Prop where
    | mk : ResultMatches ctx b.params a.params → ResultMatches ctx a.results b.results →
        FuncMatches ctx a b

  inductive StorageMatches : Context → StorageType → StorageType → Prop where
    | val : ValMatches ctx a b → StorageMatches ctx (.val a) (.val b)
    | i8 : StorageMatches ctx .i8 .i8
    | i16 : StorageMatches ctx .i16 .i16

  inductive FieldMatches : Context → FieldType → FieldType → Prop where
    | mk : a.mutable = b.mutable → StorageMatches ctx a.storage b.storage →
        (a.mutable = true → StorageMatches ctx b.storage a.storage) → FieldMatches ctx a b

  inductive FieldsMatches : Context → List FieldType → List FieldType → Prop where
    | nil : FieldsMatches ctx fields []
    | cons : FieldMatches ctx a b → FieldsMatches ctx as bs →
        FieldsMatches ctx (a :: as) (b :: bs)

  inductive CompMatches : Context → CompType → CompType → Prop where
    | func : FuncMatches ctx a b → CompMatches ctx (.func a) (.func b)
    | struct_ : FieldsMatches ctx as bs → CompMatches ctx (.struct_ as) (.struct_ bs)
    | array : FieldMatches ctx a b → CompMatches ctx (.array a) (.array b)
end

theorem RefMatches.nullability (h : RefMatches ctx a b) :
    a.nullable = true → b.nullable = true := by cases h; assumption

theorem RefMatches.heap (h : RefMatches ctx a b) : HeapMatches ctx a.heap b.heap := by
  cases h; assumption

theorem FuncMatches.params (h : FuncMatches ctx a b) : ResultMatches ctx b.params a.params := by
  cases h; assumption

theorem FuncMatches.results (h : FuncMatches ctx a b) : ResultMatches ctx a.results b.results := by
  cases h; assumption

theorem FieldMatches.mutable (h : FieldMatches ctx a b) : a.mutable = b.mutable := by
  cases h; assumption

theorem FieldMatches.covariant (h : FieldMatches ctx a b) :
    StorageMatches ctx a.storage b.storage := by
  cases h; assumption

theorem FieldMatches.invariant (h : FieldMatches ctx a b) :
    a.mutable = true → StorageMatches ctx b.storage a.storage := by cases h; assumption


theorem RefMatches.refl (ctx : Context) (a : RefType) : RefMatches ctx a a :=
  ⟨id, .refl⟩

theorem RefMatches.trans (ab : RefMatches ctx a b) (bc : RefMatches ctx b c)
    (valid : HeapValid ctx b.heap) : RefMatches ctx a c :=
  ⟨fun h => bc.nullability (ab.nullability h), .trans valid ab.heap bc.heap⟩

theorem nonNull_matches_nullable (ctx : Context) (heap : HeapType) :
    RefMatches ctx ⟨false, heap⟩ ⟨true, heap⟩ := ⟨by simp, .refl⟩

theorem nullable_not_nonNull (ctx : Context) (a b : HeapType) :
    ¬ RefMatches ctx ⟨true, a⟩ ⟨false, b⟩ := by
  intro h
  have := h.nullability rfl
  contradiction

end Wasm.Types
