import Wasm.Elements
import Wasm.ReferenceScope

namespace Wasm

inductive ImportDesc where
  | func (typeIdx : Nat)
  | tag (typeIdx : Nat)
  | global (type : GlobalType)
  | memory (type : MemoryType)
  | table (type : TableType)
  deriving DecidableEq, Repr

structure Import where
  moduleName : String
  name : String
  desc : ImportDesc
  deriving DecidableEq, Repr

inductive ExternIdx where
  | func (index : Nat)
  | tag (index : Nat)
  | global (index : Nat)
  | memory (index : Nat)
  | table (index : Nat)
  deriving DecidableEq, Repr

structure Export where
  name : String
  desc : ExternIdx
  deriving DecidableEq, Repr

structure Global where
  type : GlobalType
  init : List Instr
  deriving BEq, Repr

/-- Source module projection for the supported instructions and module entities. -/
structure Module where
  types : TypeContext := []
  imports : List Import := []
  funcs : List Func := []
  tags : List Nat := []
  globals : List Global := []
  mems : List MemoryType := []
  datas : List Data := []
  tables : List Table := []
  elems : List Elem := []
  start : Option Nat := none
  exports : List Export := []
  typeGroups : List Types.RecType := []
  deriving BEq, Repr

def Module.importedFuncIndices (module : Module) : List Nat :=
  module.imports.filterMap fun entry => match entry.desc with
    | .func x => some x
    | _ => none

def Module.importedTagIndices (module : Module) : List Nat :=
  module.imports.filterMap fun entry => match entry.desc with
    | .tag x => some x
    | _ => none

def tagSignature? (types : TypeContext) (index : Nat) : Option FuncType := do
  let ft ← types.func? (index)
  if ft.results.isEmpty then some ft else none

def Module.importedGlobals (module : Module) : List GlobalType :=
  module.imports.filterMap fun entry => match entry.desc with
    | .global type => some type
    | _ => none

def Module.importedMemories (module : Module) : List MemoryType :=
  module.imports.filterMap fun entry => match entry.desc with
    | .memory type => some type
    | _ => none

def Module.importedTables (module : Module) : List TableType :=
  module.imports.filterMap fun entry => match entry.desc with
    | .table type => some type
    | _ => none

def expressionFuncIndices (code : List Instr) : List Nat :=
  code.filterMap fun i => match i with
    | .refFunc x => some x
    | _ => none

/-- Function references declared outside function bodies, including function exports. -/
def Module.declaredRefs (module : Module) : List Nat :=
  (module.globals.flatMap fun global => expressionFuncIndices global.init) ++
  (module.tables.flatMap fun table => expressionFuncIndices table.init) ++
  (module.elems.flatMap fun elem =>
    elem.init.flatMap expressionFuncIndices ++ match elem.mode with
      | .active _ offset => expressionFuncIndices offset
      | _ => []) ++
  (module.exports.filterMap fun entry => match entry.desc with
    | .func x => some x
    | _ => none)

def Module.context? (module : Module) : Option FunctionContext := do
  let resolved ← Types.resolveSection? [] module.typeGroups
  let imported ← module.importedFuncIndices.mapM fun x => module.types.func? (x)
  let defined ← module.funcs.mapM fun function => module.types.func? (function.typeIdx)
  let tags ← (module.importedTagIndices ++ module.tags).mapM (tagSignature? module.types)
  let context : FunctionContext :=
    { types := module.types, funcs := imported ++ defined, tags,
      globals := module.importedGlobals ++ module.globals.map Global.type,
      mems := module.importedMemories ++ module.mems, dataCount := module.datas.length,
      tables := module.importedTables ++ module.tables.map Table.type,
      elems := module.elems.map Elem.kind, declaredRefs := module.declaredRefs,
      definedTypes := resolved,
      funcTypeIndices := if module.typeGroups.isEmpty then [] else
        module.importedFuncIndices ++ module.funcs.map Func.typeIdx,
      elemTypes := if module.elems.all Elem.nullable then [] else module.elems.map Elem.refType }
  return context

def Module.referencesInScope (module : Module) : Bool :=
  let count := module.typeGroups.flatten.length
  let val := ValType.referencesInScope count
  let code := instructionsInScope count
  module.types.all (fun type => (Types.embedComposite type).valTypes.all
    (fun type => (Types.projectVal type).any val)) &&
    module.imports.all (fun entry => match entry.desc with
      | .global type => val type.valType
      | .table type => heapInScope count type.kind
      | _ => true) &&
    module.funcs.all (fun function => function.locals.all val && code function.body) &&
    module.globals.all (fun global => val global.type.valType && code global.init) &&
    module.tables.all (fun table => heapInScope count table.type.kind && code table.init) &&
    module.elems.all (fun elem => heapInScope count elem.kind && elem.init.all code)

inductive GlobalSeqTyping : FunctionContext → List Global → Prop where
  | empty : GlobalSeqTyping context []
  | cons (ht : RuntimeSeqTyping context [] global.init [] [global.type.valType])
      (hc : ∀ i ∈ global.init, ConstantInstr context.globals i)
      (hr : GlobalSeqTyping
        { context with globals := context.globals ++ [global.type] } rest) :
      GlobalSeqTyping context (global :: rest)

def ExternIdx.Valid (context : FunctionContext) : ExternIdx → Prop
  | .func x => x < context.funcs.length
  | .tag x => x < context.tags.length
  | .global x => x < context.globals.length
  | .memory x => x < context.mems.length
  | .table x => x < context.tables.length

instance (context : FunctionContext) (index : ExternIdx) : Decidable (index.Valid context) := by
  cases index <;> unfold ExternIdx.Valid <;> infer_instance

/-- Declarative whole-module validation. Function bodies use the existing typing judgments;
global initializers see imported and previously defined globals only.
-/
structure ModuleTyping (module : Module) (context : FunctionContext) : Prop where
  context_eq : module.context? = some context
  imported_memories : ∀ memory ∈ module.importedMemories, memory.Valid
  memories : ∀ memory ∈ module.mems, memory.Valid
  globals : GlobalSeqTyping { context with globals := module.importedGlobals } module.globals
  functions : ∀ function ∈ module.funcs, ∃ ft,
    FuncTyping module.types context.funcs context.globals context.mems context.dataCount
      (tables := context.tables) (elems := context.elems)
      (declaredRefs := context.declaredRefs) function ft
      (definedTypes := context.definedTypes) (funcTypeIndices := context.funcTypeIndices)
      (elemTypes := context.elemTypes) (tags := context.tags)
  data : ∀ segment ∈ module.datas, DataTyping context segment
  exports : ∀ entry ∈ module.exports, entry.desc.Valid context
  export_names : (module.exports.map Export.name).Nodup
  start : ∀ x ∈ module.start, context.funcs[x]? = some ⟨[], []⟩
  imported_tables : ∀ table ∈ module.importedTables, table.Valid
  tables : ∀ table ∈ module.tables,
    TableTyping { context with globals := module.importedGlobals } table
  elements : ∀ elem ∈ module.elems, ElemTyping context elem
  type_groups : module.typeGroups ≠ [] →
    Types.TypeSectionValid [] module.typeGroups context.definedTypes ∧
      module.typeGroups.flatten.map Types.SubType.body = module.types.map Types.embedComposite
  reference_scope : module.referencesInScope = true

def Module.Valid (module : Module) : Prop := ∃ context, ModuleTyping module context

/-- Validation is supplied as a kernel-checked proof; no algorithmic body validator is assumed. -/
abbrev ValidatedModule := { module : Module // module.Valid }

end Wasm
