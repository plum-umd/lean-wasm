import Wasm.TypeValidation
import Wasm.Syntax

namespace Wasm.Types

def embedKind (heap : Wasm.RefKind) : HeapType := heap

/-- Preserve heap type and nullability when embedding executable value types. -/
def embedVal : Wasm.ValType → ValType
  | .i32 => .i32
  | .i64 => .i64
  | .f32 => .f32
  | .f64 => .f64
  | .v128 => .v128
  | .ref kind => .ref true kind
  | .refNonNull heap => .ref false heap

def projectVal : ValType → Option Wasm.ValType
  | .i32 => some .i32
  | .i64 => some .i64
  | .f32 => some .f32
  | .f64 => some .f64
  | .v128 => some .v128
  | .ref true heap => some (.ref heap)
  | .ref false heap => some (.refNonNull heap)
  | _ => none

def embedFunc (type : Wasm.FuncType) : FuncType :=
  ⟨type.params.map embedVal, type.results.map embedVal⟩

def embedComposite : Wasm.CompositeType → CompType
  | .func type => .func (embedFunc type)
  | .struct_ fields => .struct_ fields
  | .array field => .array field

@[simp] theorem project_embed (type : Wasm.ValType) :
    projectVal (embedVal type) = some type := by
  cases type with
  | i32 => rfl
  | i64 => rfl
  | f32 => rfl
  | f64 => rfl
  | v128 => rfl
  | ref kind => rfl
  | refNonNull heap => rfl

theorem embedVal_injective : Function.Injective embedVal := by
  intro a b h
  have := congrArg projectVal h
  simpa using this

def legacyDefaultable : Wasm.ValType → Bool
  | .refNonNull _ => false
  | _ => true

@[simp] theorem embed_defaultable (type : Wasm.ValType) :
    (embedVal type).defaultable = legacyDefaultable type := by
  cases type <;> rfl

theorem embed_matches (ctx : Context) (type : Wasm.ValType) :
    ValMatches ctx (embedVal type) (embedVal type) := by
  cases type with
  | i32 => exact .i32
  | i64 => exact .i64
  | f32 => exact .f32
  | f64 => exact .f64
  | v128 => exact .v128
  | ref kind => exact .ref (RefMatches.refl ctx ⟨true, kind⟩)
  | refNonNull heap => exact .ref (RefMatches.refl ctx ⟨false, heap⟩)

end Wasm.Types
