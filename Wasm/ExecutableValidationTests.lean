import Wasm.ExecutableValidationSoundness

namespace Wasm.Validation.Tests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"validator: {message}")

private def sample (body : List Instr) (results : List ValType := [.i32])
    (params : List ValType := []) (locals : List ValType := []) : Module :=
  { types := [⟨params, results⟩], funcs := [⟨0, locals, body⟩],
    exports := [⟨"f", .func 0⟩] }

private def rejected : Result Unit → Bool
  | .error (.invalid _) => true
  | _ => false

private def unsupported : Result Unit → Bool
  | .error (.unsupported _) => true
  | _ => false

#eval do
  check ((validate (sample [.localGet 0, .const (.i32 1), .binop .i32 .add]
    [.i32] [.i32])).isOk) "arithmetic"
  check ((validate (sample [.localGet 0, .localTee 1, .localSet 1, .localGet 1]
    [.i64] [.i64] [.i64])).isOk) "locals"
  check ((validate (sample [.const (.i64 1), .intConvert .wrapI64])).isOk) "conversion"
  check ((validate (sample [.const (.i32 1), .const (.i32 2), .const (.i32 0),
    .select none])).isOk) "select"
  check ((validate (sample [.const (.i64 1), .drop] [])).isOk) "drop"
  check ((validate (sample [.const (.i64 1), .const (.i32 2), .return_])).isOk)
    "return may discard the stack prefix"
  check ((validate (sample [.unreachable] [.i32, .i64])).isOk) "terminal stack polymorphism"
  let calls : Module := {
    types := [⟨[.i32], [.i32]⟩]
    funcs := [⟨0, [], [.localGet 0, .call 1]⟩, ⟨0, [], [.localGet 0]⟩] }
  check ((validate calls).isOk) "forward direct call"
  for m in [
    sample [.binop .i32 .add],
    sample [.const (.i32 1), .binop .i32 .add],
    sample [.const (.i32 1), .const (.i64 1), .binop .i32 .add],
    sample [.const (.i64 1)],
    sample [.const (.i32 1), .const (.i32 2)],
    sample [.localGet 0],
    sample [.localSet 0] [],
    sample [.localGet 0, .localSet 1] [] [.i32] [.i64],
    sample [.call 1],
    sample [.call 0] [.i32] [.i32],
    sample [.return_],
    sample [.const (.i64 1), .return_],
    sample [.drop] [],
    sample [.const (.i32 1), .const (.i64 1), .const (.i32 0), .select none],
    sample [.const (.i32 1), .const (.i32 2), .const (.i64 0), .select none]
  ] do check (rejected (validate m)) s!"reject bad body {repr m.funcs}"
  let m := sample [.const (.i32 1)]
  check (rejected (validate {m with funcs := [⟨1, [], []⟩]})) "unknown type"
  check (rejected (validate {m with exports := [⟨"f", .func 1⟩]})) "unknown export"
  check (rejected (validate {m with exports := m.exports ++ m.exports})) "duplicate export"
  check (rejected (validate {m with start := some 0})) "start must have void signature"
  check ((validate {sample [] [] with start := some 0}).isOk) "void start"
  check ((validate {m with mems := [⟨.i32, 0, none⟩]}).isOk) "memory supported"
  check ((validate (sample [.unreachable, .const (.i32 1)])).isOk) "dead code checked"
  check (unsupported (validate (sample [.binop .i32 .add, .select (some [.refNonNull .func])])))
    "preflight unsupported code before reporting invalid"
  check ((validate (sample [.localGet 0] [.ref .func] [.ref .func])).isOk)
    "nullable reference parameters and results"

#eval do
  check ((validate (sample [.block (.val (some .i32))
    [.const (.i32 7), .br 0, .drop, .const (.i32 8)]])).isOk) "branch dead suffix"
  check ((validate (sample [.const (.i32 1), .if_ (.val (some .i32))
    [.const (.i32 2)] [.const (.i32 3)]])).isOk) "both if arms"
  check ((validate (sample [.block (.val none)
    [.const (.i32 4), .br 1], .const (.i32 5)])).isOk) "branch to function label"
  for t in [ValType.i32, .i64] do
    check ((validate (sample [.unreachable, .select none, .intUnary t .popcnt] [t])).isOk)
      "unknown select result may be either integer type"
    check ((validate (sample [.unreachable, .const (.i32 0), .select none] [t])).isOk)
      "unknown select operands with known condition"
  for m in [
    sample [.const (.i32 1), .block (.val none) [.eqz .i32, .drop]] [],
    sample [.unreachable, .block (.val none) [.binop .i32 .add, .drop]] [],
    sample [.unreachable, .const (.i32 1), .binop .i64 .add, .drop] [],
    sample [.unreachable, .const (.i32 1)] [],
    sample [.unreachable, .localGet 99],
    sample [.unreachable, .call 99],
    sample [.const (.i32 0), .if_ (.val (some .i32)) [.const (.i32 1)] []],
    sample [.block (.val none) [.br 2]] [],
    sample [.block (.val none) [.brIf 0]] [],
    sample [.block (.val none) [.const (.i64 0), .brIf 0]] [],
    sample [.block (.val (some .i64))
      [.block (.val (some .i32)) [.unreachable, .brTable [0] 1], .drop]] []
  ] do check (rejected (validate m)) "structured or dead-code rejection"
  let parameterLoop : Module := {
    types := [⟨[], [.i64]⟩, ⟨[.i32], [.i64]⟩]
    funcs := [⟨0, [], [.const (.i32 1), .loop (.typeIdx 1) [.drop, .const (.i64 9)]]⟩] }
  check ((validate parameterLoop).isOk) "loop parameters"
  check (rejected (validate {parameterLoop with funcs := [⟨0, [],
    [.const (.i32 1), .loop (.typeIdx 1) [.const (.i64 9), .br 0]]⟩]}))
    "loop label takes parameters, not results"
  check (unsupported (validate (sample [.block (.val (some (.refNonNull .func))) [.unreachable]])))
    "nonnullable block signature unsupported"

private def indirectModule : Module := {
  types := [⟨[.i32], [.i32]⟩, ⟨[], [.i32]⟩]
  funcs := [⟨0, [], [.localGet 0]⟩,
    ⟨1, [], [.const (.i32 7), .const (.i32 0), .callIndirect 0 0]⟩]
  tables := [⟨⟨.i32, 1, some 2, .func, true⟩, [.refNull .func]⟩]
  elems := [{init := [[.refFunc 0]], mode := .active 0 [.const (.i32 0)]}] }

#eval do
  check ((validate indirectModule).isOk) "table, active element, and indirect call"
  for mode in [ElemMode.passive, .declarative] do
    check ((validate {indirectModule with elems := [{init := [[.refFunc 0]], mode}]}).isOk)
      "passive and declarative function elements"
  check ((validate {indirectModule with elems :=
    [{init := [[.refNull .func]], mode := .active 0 [.const (.i32 0)]}]}).isOk)
    "nullable element initializer"
  for instruction in [Instr.callIndirect 1 0, .callIndirect 0 99] do
    check (rejected (validate {indirectModule with funcs := [⟨1, [],
      [.unreachable, instruction]⟩]})) "invalid indirect indices, even in unreachable code"
  for elem in ([
    {init := [[.refFunc 99]], mode := ElemMode.passive},
    {init := [[.refFunc 0]], mode := .active 1 [.const (.i32 0)]},
    {init := [[.refFunc 0]], mode := .active 0 [.const (.i64 0)]}
  ] : List Elem) do check (rejected (validate {indirectModule with elems := [elem]})) "bad element"
  check (rejected (validate {indirectModule with
    tables := [⟨⟨.i32, 2, some 1, .func, true⟩, [.refNull .func]⟩]})) "invalid limits"
  check (rejected (validate {indirectModule with
    elems := [{init := [[.refNull .extern]]}]})) "element expression type mismatch"
  check ((validate {indirectModule with
    elems := [{kind := .extern, init := [[.refNull .extern]]}]}).isOk)
    "passive external elements"
  check (unsupported (validate {indirectModule with funcs := [⟨1, [],
    [.callIndirect 99 0, .select (some [.refNonNull .func]), .drop]⟩]}))
    "unsupported instructions preflight"

example : indirectModule.Valid := validate_sound (by
  have h : (validate indirectModule).isOk = true := by decide +kernel
  cases he : validate indirectModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

private def referenceModule : Module := {
  types := [⟨[], [.ref .func]⟩]
  funcs := [⟨0, [.ref .func], [.refFunc 0, .localTee 0, .drop,
    .localGet 0, .const (.i32 1), .tableGrow 0, .drop,
    .const (.i32 0), .localGet 0, .tableSet 0,
    .const (.i32 0), .localGet 0, .const (.i32 1), .tableFill 0,
    .const (.i32 0), .const (.i32 0), .const (.i32 1), .tableCopy 0 0,
    .const (.i32 0), .const (.i32 0), .const (.i32 1), .tableInit 0 0,
    .elemDrop 0, .const (.i32 0), .tableGet 0]⟩]
  tables := [⟨⟨.i32, 1, none, .func, true⟩, [.refNull .func]⟩]
  elems := [{init := [[.refFunc 0]]}]
  exports := [⟨"f", .func 0⟩] }

#eval do
  check ((validate referenceModule).isOk) "references, locals, and scalar/bulk table operations"
  for kind in [Types.HeapType.func, .extern] do
    check ((validate (sample [.refNull kind, .refNull kind, .const (.i32 0),
      .select (some [.ref kind])] [.ref kind])).isOk) "reference typed select"
    check ((validate (sample [.localGet 0, .refIsNull] [.i32] [.ref kind])).isOk)
      "reference null test"
  check ((validate (sample [.unreachable, .refIsNull])).isOk) "dead reference operand"
  for m in [
    sample [.refNull .func] [.ref .extern],
    sample [.const (.i32 0), .refIsNull],
    sample [.refIsNull],
    sample [.unreachable, .const (.i32 0), .refIsNull],
    sample [.refNull .func, .refNull .func, .const (.i32 0), .select none] [.ref .func],
    sample [.refNull .func, .refNull .extern, .const (.i32 0),
      .select (some [.ref .func])] [.ref .func],
    {sample [.refFunc 0] [.ref .func] with exports := []},
    sample [.unreachable, .refFunc 99] [.ref .func]
  ] do check (rejected (validate m)) "reference type, declaration, or operand rejection"

private theorem referenceModule_valid : referenceModule.Valid := validate_sound (by
  have h : (validate referenceModule).isOk = true := by decide +kernel
  cases he : validate referenceModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

-- Kernel-reduced successes can be used independently of the executable implementation.
example : (sample [.block (.val (some .i32))
    [.const (.i32 7), .br 0, .drop, .const (.i32 8)]]).Valid := validate_sound (by rfl)

example : (sample [.const (.i32 40), .const (.i32 2), .binop .i32 .add]).Valid :=
  validate_sound (by rfl)

private def importModule : Module := {
  types := [⟨[], [.i32]⟩]
  imports := [⟨"provider", "f", .func 0⟩,
    ⟨"provider", "t", .table ⟨.i64, 0, some 4, .func, true⟩⟩]
  funcs := [⟨0, [], [.const (.i64 0), .tableGet 0, .drop, .call 0]⟩]
  exports := [⟨"imported", .func 0⟩, ⟨"defined", .func 1⟩, ⟨"table", .table 0⟩] }

#eval do
  check ((validate importModule).isOk) "function/table imports and their index prefixes"
  check (rejected (validate {importModule with
    imports := [⟨"m", "f", .func 99⟩]})) "unknown imported function type"
  check (rejected (validate {importModule with
    imports := [⟨"m", "t", .table ⟨.i32, 2, some 1, .func, true⟩⟩]}))
    "invalid imported table limits"
  for desc in [ImportDesc.memory ⟨.ref .func, 0, none⟩, .global ⟨.const, .refNonNull .func⟩,
    .table ⟨.i32, 0, none, .func, false⟩] do
    check (unsupported (validate {importModule with imports := [⟨"m", "x", desc⟩]}))
      "unsupported import kinds and table reference forms"

private theorem importModule_valid : importModule.Valid := validate_sound (by
  have h : (validate importModule).isOk = true := by decide +kernel
  cases he : validate importModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

private def globalModule : Module := {
  types := [⟨[], [.i32]⟩]
  imports := [⟨"m", "seed", .global ⟨.const, .i32⟩⟩,
    ⟨"m", "reference", .global ⟨.var, .ref .extern⟩⟩]
  globals := [
    ⟨⟨.const, .i32⟩, [.globalGet 0, .const (.i32 2), .binop .i32 .add]⟩,
    ⟨⟨.var, .i32⟩, [.const (.i32 5)]⟩,
    ⟨⟨.const, .ref .func⟩, [.refFunc 0]⟩]
  funcs := [⟨0, [], [.globalGet 2, .globalSet 3, .globalGet 3]⟩]
  exports := [⟨"f", .func 0⟩, ⟨"g", .global 2⟩] }

#eval do
  check ((validate globalModule).isOk) "globals, imports, constant arithmetic, and mutation"
  check (rejected (validate {globalModule with globals := [
    ⟨⟨.const, .i32⟩, [.globalGet 0]⟩,
    ⟨⟨.const, .i32⟩, [.globalGet 3]⟩]})) "forward global initializer read"
  check (rejected (validate {globalModule with globals := [
    ⟨⟨.const, .ref .extern⟩, [.globalGet 1]⟩]})) "mutable imported initializer read"
  check (rejected (validate {globalModule with globals := [
    ⟨⟨.const, .i32⟩, [.const (.i32 1), .nop]⟩]})) "nonconstant initializer"
  check (unsupported (validate {globalModule with globals := [
    ⟨⟨.const, .refNonNull .func⟩, [.refFunc 0]⟩]})) "nonnullable global unsupported"

private theorem globalModule_valid : globalModule.Valid := validate_sound (by
  have h : (validate globalModule).isOk = true := by decide +kernel
  cases he : validate globalModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

#print axioms globalModule_valid
#print axioms Wasm.Validation.checkGlobals_sound
#print axioms Wasm.Validation.checkConstantInstruction_sound

#print axioms importModule_valid

#print axioms referenceModule_valid
private def memoryModule : Module := {
  types := [⟨[], []⟩]
  imports := [⟨"m", "memory", .memory ⟨.i32, 1, some 2⟩⟩]
  mems := [⟨.i64, 0, some 1⟩]
  datas := [{bytes := #[], mode := .passive},
    {bytes := #[], mode := .active 1 [.const (.i64 0), .const (.i64 0), .binop .i64 .add]}]
  funcs := [⟨0, [], [
    .const (.i32 0), .load .i64_8S 0 ⟨0, 0⟩, .drop,
    .const (.i64 0), .const (.i32 42), .store .i32_16 1 ⟨1, 0⟩,
    .memorySize 0, .drop, .const (.i64 0), .memoryGrow 1, .drop,
    .const (.i64 0), .const (.i32 0), .const (.i64 0), .memoryFill 1,
    .const (.i64 0), .const (.i32 0), .const (.i32 0), .memoryCopy 1 0,
    .const (.i32 0), .const (.i32 0), .const (.i32 0), .memoryInit 0 0,
    .dataDrop 0]⟩] }

#eval do
  check ((validate memoryModule).isOk) "memory imports, memory64, bulk operations and data"
  check (rejected (validate {memoryModule with mems := [⟨.i64, 2, some 1⟩]}))
    "invalid defined memory limits"
  check (rejected (validate {memoryModule with
    imports := [⟨"m", "memory", .memory ⟨.i32, 2, some 1⟩⟩]}))
    "invalid imported memory limits"
  check (rejected (validate {memoryModule with datas := [
    {bytes := #[], mode := .active 1 [.const (.i32 0)]}]})) "data offset address type"

private theorem memoryModule_valid : memoryModule.Valid := validate_sound (by
  have h : (validate memoryModule).isOk = true := by decide +kernel
  cases he : validate memoryModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

#print axioms memoryModule_valid
#print axioms Wasm.Validation.checkData_sound
#print axioms Wasm.Validation.validate_sound
#print axioms Wasm.Validation.checkCode_sound
#print axioms Wasm.Validation.checkScoped_sound
#print axioms Wasm.Validation.checkTable_sound
#print axioms Wasm.Validation.checkElem_sound

end Wasm.Validation.Tests
