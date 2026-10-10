import Std

/-!
Function/external heap types and iso-recursive function type groups for Wasm 3.0.
Runtime syntax embeds these types through `TypeEmbedding`.
https://webassembly.github.io/spec/core/syntax/types.html
https://webassembly.github.io/spec/core/valid/conventions.html
-/

namespace Wasm.Types

mutual
  /-- `recIdx` and `defined` are semantic forms; `bot` is validation-only. -/
  inductive HeapType where
    | func | nofunc | extern | noextern | bot
    | typeIdx (index : Nat)
    | recIdx (index : Nat)
    | defined (group : List SubType) (index : Nat)
    deriving BEq, Repr

  inductive ValType where
    | i32 | i64 | f32 | f64 | bot
    | ref (nullable : Bool) (heap : HeapType)
    deriving BEq, Repr

  /-- The function-only projection of `sub final? supers* comptype`. -/
  inductive SubType where
    | func (isFinal : Bool) (supers : List HeapType) (params results : List ValType)
    deriving BEq, Repr
end


structure RefType where
  nullable : Bool
  heap : HeapType
  deriving BEq, Repr

structure FuncType where
  params : List ValType
  results : List ValType
  deriving BEq, Repr

abbrev RecType := List SubType

structure DefinedType where
  group : RecType
  index : Nat
  deriving BEq, Repr

def DefinedType.heap (type : DefinedType) : HeapType := .defined type.group type.index
def RefType.val (type : RefType) : ValType := .ref type.nullable type.heap
def RefType.nonNull (type : RefType) : RefType := { type with nullable := false }
def RefType.difference (a b : RefType) : RefType :=
  { a with nullable := a.nullable && !b.nullable }

def SubType.isFinal : SubType → Bool
  | .func final _ _ _ => final
def SubType.supers : SubType → List HeapType
  | .func _ supers _ _ => supers
def SubType.body : SubType → FuncType
  | .func _ _ params results => ⟨params, results⟩
def FuncType.sub (type : FuncType) (isFinal : Bool := true)
    (supers : List HeapType := []) : SubType := .func isFinal supers type.params type.results

def ValType.mapHeap (f : HeapType → HeapType) : ValType → ValType
  | .ref nullable heap => .ref nullable (f heap)
  | type => type
def SubType.mapHeap (f : HeapType → HeapType) : SubType → SubType
  | .func final supers params results =>
    .func final (supers.map f) (params.map (.mapHeap f)) (results.map (.mapHeap f))

mutual
  /-- Parallel substitution of module indices, also under recursive-group binders. -/
  def HeapType.substTypes (f : Nat → HeapType) : HeapType → HeapType
    | .typeIdx x => f x
    | .defined group i => .defined (group.map (.substTypes f)) i
    | heap => heap
  def ValType.substTypes (f : Nat → HeapType) : ValType → ValType
    | .ref nullable heap => .ref nullable (heap.substTypes f)
    | type => type
  def SubType.substTypes (f : Nat → HeapType) : SubType → SubType
    | .func final supers params results =>
      .func final (supers.map (.substTypes f))
        (params.map (.substTypes f)) (results.map (.substTypes f))
end

/-- Recursive substitution stops at nested defined types, which bind their own indices. -/
def HeapType.substRecs (f : Nat → HeapType) : HeapType → HeapType
  | .recIdx i => f i
  | heap => heap

def rollIndex (base count : Nat) (x : Nat) : HeapType :=
  if base ≤ x ∧ x < base + count then .recIdx (x - base) else .typeIdx x
def RecType.roll (group : RecType) (base : Nat) : RecType :=
  group.map (.substTypes (rollIndex base group.length))
def RecType.projections (group : RecType) : List DefinedType :=
  (List.range group.length).map fun i => ⟨group, i⟩
def RecType.rollTypes (group : RecType) (base : Nat) : List DefinedType :=
  (group.roll base).projections

def unrollIndex (group : RecType) (i : Nat) : HeapType :=
  if i < group.length then .defined group i else .recIdx i
def RecType.unroll (group : RecType) : RecType :=
  group.map (.mapHeap (.substRecs (unrollIndex group)))
def DefinedType.unroll? (type : DefinedType) : Option SubType :=
  (type.group.unroll)[type.index]?
def DefinedType.expand? (type : DefinedType) : Option FuncType := type.unroll?.map SubType.body

mutual
  /-- Closing substitutes already closed context entries; missing indices fail explicitly. -/
  def HeapType.close? (types : List DefinedType) : HeapType → Option HeapType
    | .typeIdx x => types[x]?.map DefinedType.heap
    | .defined group i => do return .defined (← group.mapM (SubType.close? types)) i
    | heap => some heap
  def ValType.close? (types : List DefinedType) : ValType → Option ValType
    | .ref nullable heap => do return .ref nullable (← heap.close? types)
    | type => some type
  def SubType.close? (types : List DefinedType) : SubType → Option SubType
    | .func final supers params results => do
      return .func final (← supers.mapM (HeapType.close? types))
        (← params.mapM (ValType.close? types)) (← results.mapM (ValType.close? types))
end

def DefinedType.close? (types : List DefinedType) (type : DefinedType) : Option DefinedType := do
  return ⟨← type.group.mapM (SubType.close? types), type.index⟩

mutual
  /-- A bounded scope check. Exhaustion rejects rather than accepting an unchecked type. -/
  def HeapType.scopedFuel : Nat → Nat → Nat → HeapType → Bool
    | 0, _, _, _ => false
    | fuel + 1, typeCount, recCount, heap => match heap with
      | .typeIdx x => x < typeCount
      | .recIdx i => i < recCount
      | .defined group i => i < group.length &&
          group.all (SubType.scopedFuel fuel typeCount group.length)
      | _ => true
  def ValType.scopedFuel : Nat → Nat → Nat → ValType → Bool
    | 0, _, _, _ => false
    | fuel + 1, typeCount, recCount, type => match type with
      | .ref _ heap => heap.scopedFuel fuel typeCount recCount
      | _ => true
  def SubType.scopedFuel : Nat → Nat → Nat → SubType → Bool
    | 0, _, _, _ => false
    | fuel + 1, typeCount, recCount, .func _ supers params results =>
      supers.all (HeapType.scopedFuel fuel typeCount recCount) &&
      params.all (ValType.scopedFuel fuel typeCount recCount) &&
      results.all (ValType.scopedFuel fuel typeCount recCount)
end

def HeapType.scoped (typeCount recCount : Nat) (heap : HeapType) : Prop :=
  ∃ fuel, heap.scopedFuel fuel typeCount recCount = true

def HeapType.closed (heap : HeapType) : Prop := heap.scoped 0 0
def DefinedType.closed (type : DefinedType) : Prop := type.heap.closed

def HeapType.isSource : HeapType → Bool
  | .func | .nofunc | .extern | .noextern | .typeIdx _ => true
  | _ => false
def ValType.isSource : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | .ref _ heap => heap.isSource
  | .bot => false
def SubType.isSource : SubType → Bool
  | .func _ supers params results =>
    supers.all (fun heap => match heap with | .typeIdx _ => true | _ => false) &&
      params.all ValType.isSource && results.all ValType.isSource

def ValType.defaultable : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | .ref nullable _ => nullable
  | .bot => false

@[simp] theorem rollIndex_internal (h : i < count) :
    rollIndex base count (base + i) = .recIdx i := by simp [rollIndex, h]
@[simp] theorem unrollIndex_internal (h : i < group.length) :
    unrollIndex group i = .defined group i := by simp [unrollIndex, h]
@[simp] theorem roll_length (group : RecType) (base : Nat) : (group.roll base).length = group.length := by
  simp [RecType.roll]
@[simp] theorem projections_length (group : RecType) : group.projections.length = group.length := by
  simp [RecType.projections]
@[simp] theorem unroll_length (group : RecType) : group.unroll.length = group.length := by
  simp [RecType.unroll]
@[simp] theorem substRecs_defined :
    (HeapType.defined group i).substRecs f = .defined group i := rfl
@[simp] theorem nonNull_defaultable (type : RefType) : type.nonNull.val.defaultable = false := rfl

end Wasm.Types
