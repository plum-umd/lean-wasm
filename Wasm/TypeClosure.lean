import Wasm.Module

namespace Wasm

def ValType.close? (types : List Types.DefinedType) (type : ValType) : Option ValType := do
  Types.projectVal (← (Types.embedVal type).close? types)

def FuncType.close? (types : List Types.DefinedType) (type : FuncType) : Option FuncType := do
  return ⟨← type.params.mapM (ValType.close? types),
    ← type.results.mapM (ValType.close? types)⟩

def GlobalType.close? (types : List Types.DefinedType) (type : GlobalType) : Option GlobalType := do
  return { type with valType := ← type.valType.close? types }

def TableType.close? (types : List Types.DefinedType) (type : TableType) : Option TableType := do
  return { type with kind := ← type.kind.close? types }

def ImportDesc.close? (types : List Types.DefinedType) : ImportDesc → Option ImportDesc
  | .func x => some (.func x)
  | .tag x => some (.tag x)
  | .global type => (type.close? types).map .global
  | .table type => (type.close? types).map .table
  | .memory type => some (.memory type)

def CompositeType.close? (types : List Types.DefinedType) : CompositeType → Option CompositeType
  | .func type => (type.close? types).map .func
  | .struct_ fields => (fields.mapM (Types.FieldType.close? types)).map .struct_
  | .array field => (field.close? types).map .array

def Module.resolvedTypes? (module : Module) : Option (List Types.DefinedType) :=
  Types.resolveSection? [] module.typeGroups

/-- Close type uses before linking. Instruction operands remain source indices and
are resolved through the instance's type map at execution. -/
def Module.close? (module : Module) : Option Module := do
  let types ← module.resolvedTypes?
  let signatures ← module.types.mapM (CompositeType.close? types)
  let imports ← module.imports.mapM fun entry => do
    return { entry with desc := ← entry.desc.close? types }
  let funcs ← module.funcs.mapM fun function => do
    return { function with locals := ← function.locals.mapM (ValType.close? types) }
  let globals ← module.globals.mapM fun global => do
    return { global with type := ← global.type.close? types }
  let tables ← module.tables.mapM fun table => do
    return { table with type := ← table.type.close? types }
  let elems ← module.elems.mapM fun elem => do
    return { elem with kind := ← elem.kind.close? types }
  return { module with types := signatures, imports, funcs, globals, tables, elems }

end Wasm
