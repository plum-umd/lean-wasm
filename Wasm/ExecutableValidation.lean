import Wasm.Module

/-!
An ordinary executable validator and separate correctness theorems for the structured-control
integer fragment. Stack lists use specification order (top at the right).
Reference: https://webassembly.github.io/spec/core/appendix/algorithm.html
-/
namespace Wasm.Validation

inductive Error where
  | invalid (message : String)
  | unsupported (message : String)
  deriving Repr, BEq

abbrev Result := Except Error

def integerType : ValType → Bool
  | .i32 | .i64 => true
  | _ => false

def numberType : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | _ => false

def supportedValueType : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 | .ref .func | .ref .extern => true
  | _ => false

def functionHeap : RefKind → Bool
  | .func => true
  | _ => false

def popOperands : List ValType → List ValType → Option (List ValType)
  | [], stack => some stack
  | t :: types, a :: stack => if t = a then popOperands types stack else none
  | _ :: _, [] => none

/-- Remove an exactly matching suffix from the operand stack. -/
def consume (input stack : List ValType) : Option (List ValType) :=
  (popOperands input.reverse stack.reverse).map List.reverse

/-- The minimal integer stack effect; `drop` and untyped `select` inspect the current stack. -/
def effect (context : FunctionContext) (i : Instr) (stack : List ValType) :
    Result (List ValType × List ValType) := do
  match i with
  | .const (.i32 _) => return ([], [.i32])
  | .const (.i64 _) => return ([], [.i64])
  | .const (.f32 _) => return ([], [.f32])
  | .const (.f64 _) => return ([], [.f64])
  | .nop => return ([], [])
  | .drop =>
    let some t := stack.getLast? | throw (.invalid "drop: missing operand")
    return ([t], [])
  | .select none =>
    let some t := stack.reverse[1]? | throw (.invalid "select: missing operand")
    if numberType t then return ([t, t, .i32], [t])
    else throw (.invalid "select requires numeric operands")
  | .select (some [t]) =>
    if supportedValueType t then return ([t, t, .i32], [t])
    else throw (.unsupported "select value type")
  | .binop t _ | .intBinary t _ =>
    if integerType t then return ([t, t], [t])
    else throw (.unsupported "noninteger instruction")
  | .eqz t =>
    if integerType t then return ([t], [.i32])
    else throw (.unsupported "noninteger instruction")
  | .intUnary t _ =>
    if integerType t then return ([t], [t])
    else throw (.unsupported "noninteger instruction")
  | .intRel t _ =>
    if integerType t then return ([t, t], [.i32])
    else throw (.unsupported "noninteger instruction")
  | .intConvert op => return ([op.inputType], [op.outputType])
  | .floatUnary width _ => return ([width.floatType], [width.floatType])
  | .floatBinary width _ => return ([width.floatType, width.floatType], [width.floatType])
  | .floatRel width _ => return ([width.floatType, width.floatType], [.i32])
  | .floatConvert op => return ([op.inputType], [op.outputType])
  | .localGet x | .localSet x | .localTee x =>
    let some t := context.locals[x]? | throw (.invalid "unknown local")
    match i with
    | .localGet _ => return ([], [t])
    | .localSet _ => return ([t], [])
    | _ => return ([t], [t])
  | .globalGet x =>
    let some type := context.globals[x]? | throw (.invalid "unknown global")
    return ([], [type.valType])
  | .globalSet x =>
    let some type := context.globals[x]? | throw (.invalid "unknown global")
    if type.mutability = .var then return ([type.valType], [])
    else throw (.invalid "global.set requires a mutable global")
  | .load op x arg =>
    let some memory := context.mems[x]? | throw (.invalid "unknown memory")
    if arg.Valid memory.addrType op.bytes then return ([memory.addrType], [op.type])
    else throw (.invalid "invalid load alignment or offset")
  | .store op x arg =>
    let some memory := context.mems[x]? | throw (.invalid "unknown memory")
    if arg.Valid memory.addrType op.bytes then return ([memory.addrType, op.type], [])
    else throw (.invalid "invalid store alignment or offset")
  | .memorySize x | .memoryGrow x | .memoryFill x =>
    let some memory := context.mems[x]? | throw (.invalid "unknown memory")
    match i with
    | .memoryGrow _ => return ([memory.addrType], [memory.addrType])
    | .memoryFill _ => return ([memory.addrType, .i32, memory.addrType], [])
    | _ => return ([], [memory.addrType])
  | .memoryCopy x y =>
    let some dst := context.mems[x]? | throw (.invalid "unknown destination memory")
    let some src := context.mems[y]? | throw (.invalid "unknown source memory")
    return ([dst.addrType, src.addrType, dst.addrType.minAddress src.addrType], [])
  | .memoryInit x y =>
    let some memory := context.mems[x]? | throw (.invalid "unknown memory")
    if y < context.dataCount then return ([memory.addrType, .i32, .i32], [])
    else throw (.invalid "unknown data segment")
  | .dataDrop y =>
    if y < context.dataCount then return ([], [])
    else throw (.invalid "unknown data segment")
  | .call x =>
    let some ft := context.funcs[x]? | throw (.invalid "unknown function")
    return (ft.params, ft.results)
  | .callIndirect x y =>
    let some table := context.tables[x]? | throw (.invalid "unknown table")
    if functionHeap table.kind then
      let some ft := context.types[y]? | throw (.invalid "unknown indirect call type")
      return (ft.params ++ [table.addrType], ft.results)
    else throw (.invalid "indirect call requires function table")
  | .refNull kind => return ([], [.ref kind])
  | .refFunc x =>
    let some _ := context.funcs[x]? | throw (.invalid "unknown function reference")
    if context.declaredRefs.contains x then return ([], [.ref .func])
    else throw (.invalid "undeclared function reference")
  | .refIsNull =>
    match stack.getLast? with
    | some (.ref kind) => return ([.ref kind], [.i32])
    | _ => throw (.invalid "ref.is_null requires a reference")
  | .tableGet x | .tableSet x | .tableSize x | .tableGrow x | .tableFill x =>
    let some table := context.tables[x]? | throw (.invalid "unknown table")
    match i with
    | .tableGet _ => return ([table.addrType], [table.refType])
    | .tableSet _ => return ([table.addrType, table.refType], [])
    | .tableGrow _ => return ([table.refType, table.addrType], [table.addrType])
    | .tableFill _ => return ([table.addrType, table.refType, table.addrType], [])
    | _ => return ([], [table.addrType])
  | .tableCopy x y =>
    let some dst := context.tables[x]? | throw (.invalid "unknown destination table")
    let some src := context.tables[y]? | throw (.invalid "unknown source table")
    if src.kind = dst.kind ∧ (src.nullable = false ∨ dst.nullable = true) then
      return ([dst.addrType, src.addrType, dst.addrType.minAddress src.addrType], [])
    else throw (.invalid "table.copy reference type mismatch")
  | .tableInit x y =>
    let some table := context.tables[x]? | throw (.invalid "unknown table")
    let some kind := context.elems[y]? | throw (.invalid "unknown element segment")
    if kind = table.kind ∧ table.nullable = true then
      return ([table.addrType, .i32, .i32], [])
    else throw (.invalid "table.init reference type mismatch")
  | .elemDrop y =>
    let some _ := context.elems[y]? | throw (.invalid "unknown element segment")
    return ([], [])
  | _ => throw (.unsupported "instruction")

/-- Pop known operands, supplying a missing prefix only in an unreachable frame. -/
def popPolymorphic (dead : Bool) : List ValType → List ValType →
    Option (List ValType × List ValType)
  | [], stack => some ([], stack)
  | t :: types, a :: stack =>
    if t = a then popPolymorphic dead types stack else none
  | types@(_ :: _), [] => if dead then some (types, []) else none

def consumePolymorphic (input stack : List ValType) (dead : Bool) :
    Option (List ValType × List ValType) :=
  (popPolymorphic dead input.reverse stack.reverse).map fun (missing, base) =>
    (missing.reverse, base.reverse)

inductive CheckedEffect where
  | normal (input output : List ValType)
  | jump (input : List ValType)
  deriving Repr

/-- Structured bodies are checked in fresh frames, separate from the enclosing stack. -/
def scopedEffect (context : FunctionContext) (labels : LabelContext) (i : Instr)
    (stack : List ValType) (candidate : ValType)
    (bodyCheck : LabelContext → List Instr → List ValType → List ValType → Bool) :
    Result CheckedEffect := do
  match i with
  | .unreachable => return .jump []
  | .return_ =>
    let some results := context.returns | throw (.invalid "return outside function")
    return .jump results
  | .br x | .brIf x =>
    let some ts := labels[x]? | throw (.invalid "unknown label")
    match i with
    | .br _ => return .jump ts
    | _ => return .normal (ts ++ [.i32]) ts
  | .brTable targets fallback =>
    let some ts := labels[fallback]? | throw (.invalid "unknown default label")
    if decide (∀ x ∈ targets, labels[x]? = some ts) then
      return .jump (ts ++ [.i32])
    else throw (.invalid "branch table label mismatch")
  | .block bt body | .loop bt body =>
    let some ft := bt.resolve context.types | throw (.invalid "unknown block type")
    let target := match i with | .loop _ _ => ft.params | _ => ft.results
    if bodyCheck (target :: labels) body ft.params ft.results then
      return .normal ft.params ft.results
    else throw (.invalid "block or loop body mismatch")
  | .if_ bt yes no =>
    let some ft := bt.resolve context.types | throw (.invalid "unknown if type")
    if bodyCheck (ft.results :: labels) yes ft.params ft.results &&
        bodyCheck (ft.results :: labels) no ft.params ft.results then
      return .normal (ft.params ++ [.i32]) ft.results
    else throw (.invalid "if arm mismatch")
  | .drop => return .normal [stack.getLast?.getD candidate] []
  | .refIsNull =>
    match stack.getLast?.getD candidate with
    | .ref kind => return .normal [.ref kind] [.i32]
    | _ => throw (.invalid "ref.is_null requires a reference")
  | .select none =>
    let t := stack.reverse[1]?.getD candidate
    if numberType t then return .normal [t, t, .i32] [t]
    else throw (.invalid "select requires numeric operands")
  | _ =>
    let (input, output) ← effect context i stack
    return .normal input output

/-- Only an untyped select with two unknown operands needs an integer choice.
All other effects have a unique concrete result type. -/
def candidates (i : Instr) (stack : List ValType) : List ValType :=
  match i with
  | .select none => if stack.reverse[1]?.isNone then [.i32, .i64, .f32, .f64] else [.i32]
  | .refIsNull => [.ref .func]
  | _ => [.i32]

/-- Fuel bounds structural recursion, not execution. The public checker supplies an AST-size bound.
An unreachable frame permits underflow but still checks every known operand and instruction. -/
def checkScoped : Nat → FunctionContext → LabelContext → List Instr → List ValType →
    Bool → List ValType → Bool
  | 0, _, _, _, _, _, _ => false
  | fuel + 1, context, labels, code, stack, dead, output =>
    match code with
    | [] => if dead then (consume stack output).isSome else decide (stack = output)
    | i :: rest =>
      (candidates i stack).any fun candidate =>
        match scopedEffect context labels i stack candidate
            (fun ls body input output => checkScoped fuel context ls body input false output) with
        | .error _ => false
        | .ok eff =>
          let required := match eff with | .normal input _ | .jump input => input
          match consumePolymorphic required stack dead with
          | none => false
          | some (_, base) => match eff with
            | .normal _ produced => checkScoped fuel context labels rest
                (base ++ produced) dead output
            | .jump _ => checkScoped fuel context labels rest [] true output

mutual
  def instructionBudget : Instr → Nat
    | .block _ body | .loop _ body => codeBudget body + 1
    | .if_ _ yes no => codeBudget yes + codeBudget no + 1
    | _ => 1
  def codeBudget : List Instr → Nat
    | [] => 1
    | i :: rest => instructionBudget i + codeBudget rest + 1
end

/-- Check code with its implicit function label and an initially reachable operand stack. -/
def checkCode (context : FunctionContext) (code : List Instr) (stack output : List ValType)
    (labels : LabelContext := context.returns.toList) : Result Unit :=
  if checkScoped (codeBudget code) context labels code stack false output then .ok ()
  else .error (.invalid "instruction or operand stack mismatch")

/-- Context used by the declarative function rule; this only constructs data. -/
def functionContext (types : TypeContext) (context : FunctionContext) (function : Func)
    (ft : FuncType) : FunctionContext :=
  { types, locals := ft.params ++ function.locals, funcs := context.funcs,
    returns := some ft.results, globals := context.globals, mems := context.mems,
    dataCount := context.dataCount, tables := context.tables, elems := context.elems,
    declaredRefs := context.declaredRefs, definedTypes := context.definedTypes,
    funcTypeIndices := context.funcTypeIndices, elemTypes := context.elemTypes }

def checkFunction (types : TypeContext) (context : FunctionContext) (function : Func) : Bool :=
  match types[function.typeIdx]? with
  | none => false
  | some ft => decide (function.Initialized ft) &&
    (checkCode (functionContext types context function ft) function.body [] ft.results).isOk

def integerBlockType : BlockType → Bool
  | .val none | .typeIdx _ => true
  | .val (some t) => supportedValueType t

mutual
  def supportedInstruction : Instr → Bool
    | .const (.i32 _) | .const (.i64 _) | .const (.f32 _) | .const (.f64 _) |
        .nop | .drop | .select none => true
    | .floatUnary _ _ | .floatBinary _ _ | .floatRel _ _ | .floatConvert _ => true
    | .select (some [t]) => supportedValueType t
    | .refNull .func | .refNull .extern | .refFunc _ | .refIsNull |
        .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _ |
        .tableCopy _ _ | .tableInit _ _ | .elemDrop _ => true
    | .load _ _ _ | .store _ _ _ | .memorySize _ | .memoryGrow _ | .memoryFill _ |
        .memoryCopy _ _ | .memoryInit _ _ | .dataDrop _ => true
    | .binop t _ | .eqz t | .intUnary t _ |
        .intBinary t _ | .intRel t _ => integerType t
    | .intConvert _ | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ |
        .call _ | .callIndirect _ _ |
        .unreachable | .return_ | .br _ | .brIf _ | .brTable _ _ => true
    | .block bt body | .loop bt body => integerBlockType bt && supportedCode body
    | .if_ bt yes no => integerBlockType bt && supportedCode yes && supportedCode no
    | _ => false
  def supportedCode : List Instr → Bool
    | [] => true
    | i :: rest => supportedInstruction i && supportedCode rest
end

def supportedHeap : RefKind → Bool
  | .func | .extern => true
  | _ => false

def defaultTableInit (kind : RefKind) (code : List Instr) : Bool :=
  match kind, code with
  | .func, [.refNull .func] | .extern, [.refNull .extern] => true
  | _, _ => false

def checkConstantInstruction (globals : List GlobalType) : Instr → Bool
  | .const (.i32 _) | .const (.i64 _) | .const (.f32 _) | .const (.f64 _) |
      .refNull _ | .refFunc _ => true
  | .binop type _ => integerType type
  | .globalGet x => match globals[x]? with
    | some type => type.mutability == .const
    | none => false
  | _ => false

def supportedTable (table : Table) : Bool :=
  integerType table.type.addrType && supportedHeap table.type.kind && table.type.nullable &&
    supportedCode table.init

def supportedElem (elem : Elem) : Bool :=
  supportedHeap elem.kind && elem.nullable && elem.init.all supportedCode &&
    match elem.mode with
    | .passive | .declarative => true
    | .active _ offset => supportedCode offset

def checkTable (context : FunctionContext) (table : Table) : Bool :=
  decide table.type.Valid &&
    (checkCode context table.init [] [table.type.refType] []).isOk &&
    table.init.all (checkConstantInstruction context.globals)

def checkElemMode (context : FunctionContext) (type : ValType) : ElemMode → Bool
  | .passive | .declarative => true
  | .active x offset => match context.tables[x]? with
    | none => false
    | some table =>
      decide (type = table.refType) &&
      (checkCode context offset [] [table.addrType] []).isOk &&
      offset.all (checkConstantInstruction context.globals)

def checkElem (context : FunctionContext) (elem : Elem) : Bool :=
  elem.init.all (fun code => (checkCode context code [] [elem.refType] []).isOk &&
    code.all (checkConstantInstruction context.globals)) &&
    checkElemMode context elem.refType elem.mode

def checkGlobals (context : FunctionContext) : List Global → Bool
  | [] => true
  | global :: rest =>
    (checkCode context global.init [] [global.type.valType] []).isOk &&
    global.init.all (checkConstantInstruction context.globals) &&
    checkGlobals {context with globals := context.globals ++ [global.type]} rest

def supportedData (data : Data) : Bool :=
  match data.mode with
  | .passive => true
  | .active _ offset => supportedCode offset

def checkData (context : FunctionContext) (data : Data) : Bool :=
  match data.mode with
  | .passive => true
  | .active x offset => match context.mems[x]? with
    | none => false
    | some memory =>
      (checkCode context offset [] [memory.addrType] []).isOk &&
      offset.all (checkConstantInstruction context.globals)

def supportedImport (entry : Import) : Bool :=
  match entry.desc with
  | .func _ => true
  | .global type => supportedValueType type.valType
  | .memory type => integerType type.addrType
  | .table type => integerType type.addrType && supportedHeap type.kind && type.nullable

def checkImport (types : TypeContext) (entry : Import) : Bool :=
  match entry.desc with
  | .func x => types[x]?.isSome
  | .global _ => true
  | .memory type => decide type.Valid
  | .table type => decide type.Valid

/-- Module features supported by this first validator. Unsupported is distinct from invalid. -/
def supportedModule (module : Module) : Bool :=
  module.imports.all supportedImport &&
    module.globals.all (fun global =>
      supportedValueType global.type.valType && supportedCode global.init) &&
    module.mems.all (fun memory => integerType memory.addrType) &&
    module.datas.all supportedData && module.tables.all supportedTable &&
    module.elems.all supportedElem &&
    module.typeGroups.isEmpty &&
    module.types.all (fun ft =>
      ft.params.all supportedValueType && ft.results.all supportedValueType) &&
    module.funcs.all (fun f => f.locals.all supportedValueType && supportedCode f.body)

def moduleChecks (module : Module) (context : FunctionContext) : Bool :=
  module.imports.all (checkImport module.types) &&
    module.funcs.all (checkFunction module.types context) &&
    module.exports.all (fun entry => decide (entry.desc.Valid context)) &&
    decide ((module.exports.map Export.name).Nodup) &&
    decide (∀ x ∈ module.start, context.funcs[x]? = some ⟨[], []⟩) &&
    module.referencesInScope && module.tables.all (checkTable {context with globals := module.importedGlobals}) &&
    module.elems.all (checkElem context) &&
    checkGlobals {context with globals := module.importedGlobals} module.globals &&
    module.mems.all (fun memory => decide memory.Valid) && module.datas.all (checkData context)

/-- Ordinary executable validation. Proofs are established separately in `validate_sound`. -/
def validate (module : Module) : Result Unit :=
  if supportedModule module then
    match module.context? with
    | none => .error (.invalid "unknown function type")
    | some context =>
      if moduleChecks module context then .ok ()
      else .error (.invalid "module validation failed")
  else .error (.unsupported "module features or value types")

end Wasm.Validation
