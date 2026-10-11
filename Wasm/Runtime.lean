import Wasm.TypeEmbedding
import Wasm.TypeChecking

/-!
Runtime structures for the supported fragment of WebAssembly 3.0.
https://webassembly.github.io/spec/core/exec/runtime.html
Module and store records are explicit projections to the currently modeled entities.
-/

namespace Wasm

/-- Source function syntax, with uncompressed local declarations and no binary encoding. -/
structure Func where
  typeIdx : Nat
  locals : List ValType
  body : List Instr
  deriving BEq, Repr

/-- Host identifiers are symbolic handles; invocation behavior is not implemented. -/
inductive FuncCode where
  | wasm (function : Func)
  | host (identifier : Nat)
  | hostTyped (identifier : Nat) (type : Types.DefinedType)
  deriving BEq, Repr

/-- A function closes over its defining module, whose functions refer back into the store. -/
structure FuncInst where
  type : FuncType
  module : ModuleInst
  code : FuncCode
  deriving BEq, Repr

structure GlobalInst where
  type : GlobalType
  value : Value
  deriving DecidableEq, Repr


abbrev Byte := BitVec 8

structure MemoryInst where
  type : MemoryType
  bytes : Array Byte
  deriving DecidableEq, Repr

structure DataInst where
  bytes : Array Byte
  deriving DecidableEq, Repr

structure TableInst where
  type : TableType
  refs : Array RefValue
  deriving DecidableEq, Repr

structure ElemInst where
  kind : RefKind
  refs : Array RefValue
  nullable : Bool := true
  deriving DecidableEq, Repr

structure TagInst where
  type : FuncType
  definedType : Types.DefinedType
  deriving DecidableEq, Repr

structure ExnInst where
  tag : TagAddr
  fields : List Value
  deriving DecidableEq, Repr

structure StructInst where
  type : Types.DefinedType
  fields : List Value
  deriving DecidableEq, Repr

structure ArrayInst where
  type : Types.DefinedType
  fields : Array Value
  deriving DecidableEq, Repr

/-- Store projection for the supported instances, with separate address spaces. -/
structure Store where
  funcs : List FuncInst := []
  globals : List GlobalInst := []
  mems : List MemoryInst := []
  datas : List DataInst := []
  tables : List TableInst := []
  elems : List ElemInst := []
  tags : List TagInst := []
  exns : List ExnInst := []
  structs : List StructInst := []
  arrays : List ArrayInst := []
  deriving BEq, Repr

def gcAllocationBudget : Nat := 1048576

/-- Parameters and locals retain static local-index order, rather than operand-stack order. -/
def ValType.defaultable : ValType → Bool
  | .refNonNull _ => false
  | _ => true

def Value.default (t : ValType) : Option Value :=
  match t with
  | .i32 => some (.i32 0)
  | .i64 => some (.i64 0)
  | .f32 => some (.f32 0)
  | .f64 => some (.f64 0)
  | .v128 => some (.v128 0)
  | .ref kind => some (.ref (.null kind))
  | .refNonNull _ => none

theorem Value.default_type (t : ValType) :
    (Value.default t).map Value.type = if t.defaultable then some t else none := by
  cases t <;> rfl

def Frame.initialize (module : ModuleInst) (args : List Value) (locals : List ValType) : Frame :=
  ⟨args.map some ++ locals.map Value.default, module⟩

theorem Frame.initialize_length (module : ModuleInst) (args : List Value) (locals : List ValType) :
    (Frame.initialize module args locals).locals.length = args.length + locals.length := by
  simp [Frame.initialize]

theorem Frame.initialize_types (module : ModuleInst) (args : List Value) (locals : List ValType) :
    (Frame.initialize module args locals).locals.map (Option.map Value.type) =
      (args.map (some ∘ Value.type) ++
        locals.map (fun t => if t.defaultable then some t else none)) := by
  simp [Frame.initialize, List.map_append, List.map_map, Function.comp_def, Value.default_type]

def ModuleInst.funcAddr? (module : ModuleInst) (index : Nat) : Option FuncAddr :=
  module.funcs[index]?

def ModuleInst.export? (module : ModuleInst) (name : String) : Option ExternAddr :=
  (module.exports.find? fun entry => entry.name == name).map ExportInst.address

def Store.func? (store : Store) (address : FuncAddr) : Option FuncInst :=
  store.funcs[address.index]?

/-- Resolve a module-local index through its address map, then through the shared store. -/
def Store.resolveFunc? (store : Store) (module : ModuleInst) (index : Nat) : Option FuncInst :=
  (module.funcAddr? index).bind store.func?

/-- Append-only allocation preserves every existing function address. -/
def Store.allocateFunc (store : Store) (function : FuncInst) : FuncAddr × Store :=
  (⟨store.funcs.length⟩, { store with funcs := store.funcs ++ [function] })

theorem Store.allocateFunc_lookup (store : Store) (function : FuncInst) :
    (store.allocateFunc function).2.func? (store.allocateFunc function).1 = some function := by
  simp [Store.allocateFunc, Store.func?]

theorem Store.allocateFunc_preserves (store : Store) (function : FuncInst) (address : FuncAddr)
    (h : address.index < store.funcs.length) :
    (store.allocateFunc function).2.func? address = store.func? address := by
  simp [Store.allocateFunc, Store.func?, List.getElem?_append, h]

/-- Referential checks only: these do not validate function bodies or instantiate a module. -/
def ModuleInst.Valid (store : Store) (module : ModuleInst) : Prop :=
  (∀ address ∈ module.funcs, ∃ function, store.func? address = some function) ∧
  (∀ address ∈ module.globals, ∃ global, store.globals[address.index]? = some global) ∧
  (∀ address ∈ module.mems, ∃ memory, store.mems[address.index]? = some memory) ∧
  (∀ address ∈ module.datas, ∃ data, store.datas[address.index]? = some data) ∧
  (∀ address ∈ module.tables, ∃ table, store.tables[address.index]? = some table) ∧
  (∀ address ∈ module.elems, ∃ elem, store.elems[address.index]? = some elem) ∧
  (module.exports.map ExportInst.name).Nodup ∧
  (∀ entry ∈ module.exports,
    match entry.address with
    | .func address => address ∈ module.funcs
    | .global address => address ∈ module.globals
    | .memory address => address ∈ module.mems
    | .table address => address ∈ module.tables
    | .tag address => address ∈ module.tags)

def FuncInst.SignatureValid (function : FuncInst) : Prop :=
  match function.code with
  | .wasm code => function.module.types.func? (code.typeIdx) = some function.type
  | .host _ => True
  | .hostTyped _ type => type.expand? = some (Types.embedFunc function.type) ∧ type.closed

def FuncType.definedType (type : FuncType) : Types.DefinedType :=
  ⟨[(Types.embedFunc type).sub], 0⟩

/-- The closed recursive type of a function; legacy signatures form singleton final groups. -/
def FuncInst.runtimeType (function : FuncInst) : Types.DefinedType :=
  let defined := match function.code with
    | .wasm code => function.module.definedTypes[code.typeIdx]?
    | .host _ => none
    | .hostTyped _ type => some type
  defined.getD function.type.definedType

/-- Function reference types come from the store. Null uses its hierarchy bottom. -/
def RefValue.type? (store : Store) : RefValue → Option ValType
  | .func address => (store.func? address).map fun function =>
      .refNonNull function.runtimeType.heap
  | .struct_ address => (store.structs[address.index]?).map fun object =>
      .refNonNull object.type.heap
  | .array address => (store.arrays[address.index]?).map fun object =>
      .refNonNull object.type.heap
  | .exn _ => some (.refNonNull .exn)
  | .extern _ | .external _ => some (.refNonNull .extern)
  | .i31 _ => some (.refNonNull .i31)
  | .host _ => some (.refNonNull .any)
  | .null heap => match heap with
    | .func | .nofunc => some (.ref .nofunc)
    | .defined group index =>
      match (Types.DefinedType.mk group index).expandComposite? with
      | some (.func _) => some (.ref .nofunc)
      | some (.struct_ _) | some (.array _) => some (.ref .none)
      | none => none
    | .extern | .noextern => some (.ref .noextern)
    | .exn | .noexn => some (.ref .noexn)
    | .any | .eq | .i31 | .struct_ | .array | .none => some (.ref .none)
    | _ => none

def Value.type? (store : Store) : Value → Option ValType
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .f32 _ => some .f32
  | .f64 _ => some .f64
  | .v128 _ => some .v128
  | .ref reference => reference.type? store

abbrev Typed (store : Store) (value : Value) (type : ValType) : Prop :=
  ∃ actual, value.type? store = some actual ∧
    Types.ValMatches {} (Types.embedVal actual) (Types.embedVal type)

def checkRuntimeHeap (a b : Types.HeapType) : Types.Checked (Types.HeapMatches {} a b) :=
  Types.checkHeap (Types.matchingBudget a b) {} a b

def searchRuntimeVal (a b : ValType) : Types.Search
    (Types.ValMatches {} (Types.embedVal a) (Types.embedVal b)) :=
  Types.searchVal (match a, b with
    | .ref a, .ref b | .refNonNull a, .ref b | .ref a, .refNonNull b
    | .refNonNull a, .refNonNull b => Types.matchingBudget a b
    | _, _ => 1) {} (Types.embedVal a) (Types.embedVal b)

def checkRuntimeVal (a b : ValType) : Types.Checked
    (Types.ValMatches {} (Types.embedVal a) (Types.embedVal b)) :=
  (searchRuntimeVal a b).toOption

/-- Unknown addresses and exhausted search remain inconclusive, never cast failures. -/
def searchValue (store : Store) (value : Value) (type : ValType) :
    Types.Search (Typed store value type) :=
  match found : value.type? store with
  | none => .inconclusive
  | some actual => (searchRuntimeVal actual type).map fun h => ⟨⟨actual, found, h.down⟩⟩

/-- Every successful check carries a derivation; inconclusive checks leave execution stuck. -/
def checkValue (store : Store) (value : Value) (type : ValType) :
    Types.Checked (Typed store value type) :=
  (searchValue store value type).toOption

theorem checkValue_sound (h : (checkValue store value type).isSome = true) :
    Typed store value type := by
  cases hc : checkValue store value type with
  | none => simp [hc] at h
  | some proof => exact proof.down

def TableType.refType (type : TableType) : ValType :=
  if type.nullable then .ref type.kind else .refNonNull type.kind

def ElemInst.refType (elem : ElemInst) : ValType :=
  if elem.nullable then .ref elem.kind else .refNonNull elem.kind

inductive ArgsTyped (store : Store) : List Value → List ValType → Prop where
  | nil : ArgsTyped store [] []
  | cons : Typed store value type → ArgsTyped store vs ts →
      ArgsTyped store (value :: vs) (type :: ts)

def checkArgs (store : Store) : (args : List Value) → (types : List ValType) →
    Types.Checked (ArgsTyped store args types)
  | [], [] => some ⟨.nil⟩
  | value :: values, type :: types => do
    let head ← checkValue store value type
    let tail ← checkArgs store values types
    return ⟨.cons head.down tail.down⟩
  | _, _ => none

def GlobalInst.Valid (store : Store) (global : GlobalInst) : Prop :=
  Typed store global.value global.type.valType

def TableInst.ReferencesValid (store : Store) (table : TableInst) : Prop :=
  ∀ reference ∈ table.refs.toList, Typed store (.ref reference) table.type.refType

def ElemInst.ReferencesValid (store : Store) (elem : ElemInst) : Prop :=
  ∀ reference ∈ elem.refs.toList, Typed store (.ref reference) elem.refType

theorem Typed.store_funcs (h : Typed store value type) (same : next.funcs = store.funcs)
    (sameStructs : next.structs = store.structs) (sameArrays : next.arrays = store.arrays) :
    Typed next value type := by
  obtain ⟨actual, found, matched⟩ := h
  refine ⟨actual, ?_, matched⟩
  cases value with
  | i32 _ | i64 _ | f32 _ | f64 _ | v128 _ => exact found
  | ref reference =>
    cases reference <;> simpa [Value.type?, RefValue.type?, Store.func?, same, sameStructs, sameArrays] using found

/-- Prepare an activation using store-dependent argument typing and optional local defaults. -/
def FuncInst.activation? (function : FuncInst) (args : List Value)
    (store : Store := {}) : Option AdminInstr :=
  match function.code with
  | .host _ | .hostTyped _ _ => none
  | .wasm code =>
    if function.module.types.func? (code.typeIdx) = some function.type then
      match checkArgs store args function.type.params with
      | none => none
      | some _ =>
        let frame := Frame.initialize function.module args code.locals
        let arity := function.type.results.length
        some (.frame arity frame [.label arity [] (instructions code.body)])
    else none

inductive Invokes (store : Store) : FuncInst → List Value → AdminInstr → Prop where
  | wasm (hs : module.types.func? (code.typeIdx) = some type)
      (ha : ArgsTyped store args type.params) :
      Invokes store ⟨type, module, .wasm code⟩ args
        (.frame type.results.length (Frame.initialize module args code.locals)
          [.label type.results.length [] (instructions code.body)])

theorem FuncInst.activation?_sound (h : function.activation? args store = some activation) :
    Invokes store function args activation := by
  cases function with
  | mk type module code =>
    cases code with
    | host id => simp [FuncInst.activation?] at h
    | hostTyped id type => simp [FuncInst.activation?] at h
    | wasm code =>
      simp only [FuncInst.activation?] at h
      split at h
      · rename_i valid
        cases hc : checkArgs store args type.params with
        | none => simp [hc] at h
        | some checked =>
          simp only [hc] at h
          cases h
          exact .wasm valid checked.down
      · cases h

/-- Completeness is conditional on successful bounded argument search. -/
theorem FuncInst.activation?_complete (h : Invokes store function args activation)
    (checked : (checkArgs store args function.type.params).isSome = true) :
    function.activation? args store = some activation := by
  cases h with
  | wasm hs ha =>
    simp only [FuncInst.activation?, hs, ↓reduceIte]
    cases hc : checkArgs store args _ with
    | none => simp [hc] at checked
    | some proof => rfl

/-- Current machine components: shared store, current frame state, and instructions. -/
structure Configuration where
  store : Store
  frame : Frame
  code : List AdminInstr
  deriving BEq, Repr

end Wasm
