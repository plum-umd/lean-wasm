import Wasm.Text.Module
import Wasm.Binary.Decode
import Wasm.NativeExecution
import Wasm.ExecutableValidationSoundness

namespace Wasm.Text

inductive Outcome where
  | passed
  | failed (message : String)
  | unsupported (message : String)
  deriving Repr, BEq

structure Report where
  outcomes : List Outcome := []
  output : List Value := []
  deriving Repr

def Report.passed (r : Report) : Nat := r.outcomes.countP (· == .passed)
def Report.failed (r : Report) : Nat := r.outcomes.countP fun
  | .failed _ => true
  | _ => false
def Report.unsupported (r : Report) : Nat := r.outcomes.countP fun
  | .unsupported _ => true
  | _ => false

private structure State where
  output : List Value := []
  store : Store := Spectest.store
  current : Option ModuleInst := none
  definition : Option ValidatedModule := none
  definitions : List (String × Option ValidatedModule) := []
  named : List (String × Option ModuleInst) := []
  registered : List (String × Option ModuleInst) := [("spectest", some Spectest.module)]

private def fromError : Error → Outcome
  | .invalid msg => .failed msg
  | .unsupported msg => .unsupported msg

private def moduleName : SExpr → Option String
  | .list (.atom "module" :: .atom id :: _) => if id.startsWith "$" then some id else none
  | _ => none

private def owner (state : State) (id : Option String) : Result ModuleInst :=
  match id with
  | none => match state.current with
    | some m => .ok m
    | none => .error (.unsupported "current module unavailable")
  | some id => match state.named.lookup id with
    | some (some m) => .ok m
    | some none => .error (.unsupported s!"module {id} unavailable")
    | none => .error (.invalid s!"unknown module {id}")

private def linkImports (state : State) (source : Module) : Result (List ExternAddr) := do
  let addresses ← source.imports.mapM fun entry => do
    let provider ← match state.registered.lookup entry.moduleName with
      | some (some provider) => pure provider
      | some none => throw (.unsupported s!"registered module {entry.moduleName} unavailable")
      | none => throw (.invalid s!"unregistered import module {entry.moduleName}")
    let some address := provider.export? entry.name |
      throw (.invalid s!"import export {entry.moduleName}.{entry.name} not found")
    return address
  let some closed := source.close? | throw (.invalid "import type closure failed")
  if decide (ImportsMatch state.store closed.types closed.imports addresses
      (source.resolvedTypes?.getD [])) then return addresses
  else throw (.invalid "import types do not match")

private def decodeModule (expr : SExpr) : Result Module := do
  let .list (.atom "module" :: fields) := expr | throw (.invalid "expected module")
  let fields := match fields with
    | .atom "definition" :: rest => rest
    | _ => fields
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  match fields with
  | .atom "quote" :: strings =>
    let mut bytes := ByteArray.empty
    for expr in strings do
      let .string fragment := expr | throw (.invalid "quoted module requires strings")
      bytes := bytes ++ fragment
    let text ← name bytes
    let commands ← (parse text).mapError Error.invalid
    let source := match commands with
      | [source@(.list (.atom "module" :: _))] => source
      | fields => SExpr.list (.atom "module" :: fields)
    return ← module source
  | .atom "binary" :: strings =>
    let mut bytes := ByteArray.empty
    for expr in strings do
      let .string fragment := expr | throw (.invalid "binary module requires strings")
      bytes := bytes ++ fragment
    match Binary.decode bytes with
    | .ok source => return source
    | .error (.malformed offset message) => throw (.invalid s!"binary offset {offset}: {message}")
    | .error (.unsupported offset message) =>
      throw (.unsupported s!"binary offset {offset}: {message}")
  | _ => module (.list (.atom "module" :: fields))

private def validateSource (expr : SExpr) : Result ValidatedModule := do
  let source ← decodeModule expr
  match hv : Validation.validate source with
  | .ok () => return ⟨source, Validation.validate_sound hv⟩
  | .error (.invalid msg) => throw (.invalid s!"validation: {msg}")
  | .error (.unsupported msg) => throw (.unsupported s!"validation: {msg}")

private def invoke (fuel callDepth : Nat) (state : State) (expr : SExpr) :
    Result (State × RunStatus) := do
  let .list (.atom "invoke" :: fields) := expr | throw (.unsupported "action")
  let (id, fields) := match fields with
    | .atom id :: rest => (some id, rest)
    | _ => (none, fields)
  let .string bytes :: args := fields | throw (.invalid "invoke requires export name")
  let m ← owner state id
  let exportName ← name bytes
  let some (.func address) := m.export? exportName |
    throw (.invalid s!"function export {exportName} not found")
  let some f := state.store.funcs[address.index]? | throw (.invalid "function address missing")
  let vs ← args.mapM fun expr => do
    let value ← constant expr
    match value with
    | .ref (.null heap) =>
      let some closed := heap.close? m.definedTypes | throw (.invalid "unknown argument heap type")
      pure (Value.ref (.null closed))
    | value => pure value
  let some _ := checkArgs state.store vs f.type.params |
    throw (.invalid "function arguments do not match")
  let activation := values vs ++ [.invoke address f.type]
  let execution := Native.run fuel ⟨state.store, ⟨[], m⟩, activation⟩ callDepth
  return ({state with
    store := execution.state.store
    output := state.output ++ execution.output}, execution.status)

private def action (fuel callDepth : Nat) (state : State) (expr : SExpr) :
    Result (State × RunStatus) := do
  match expr with
  | .list (.atom "get" :: fields) =>
    let (id, fields) := match fields with
      | .atom id :: rest => (some id, rest)
      | _ => (none, fields)
    let [.string bytes] := fields | throw (.invalid "get requires one export name")
    let m ← owner state id
    let exportName ← name bytes
    let some (.global address) := m.export? exportName |
      throw (.invalid s!"global export {exportName} not found")
    let some global := state.store.global? address | throw (.invalid "global address missing")
    return (state, .finished [global.value])
  | _ => invoke fuel callDepth state expr

private inductive Expected where
  | value (value : Value)
  | null
  | func
  | extern
  | i31
  | struct_
  | array
  | eq
  | any
  | nan (width : NumWidth) (canonical : Bool)
  | vector (width : NumWidth) (lanes : List Expected)
  | either (choices : List Expected)
  deriving Repr

private instance : Nonempty Expected := ⟨.null⟩

private partial def expected : SExpr → Result Expected
  | .list (.atom "either" :: choices) => do
    if choices.isEmpty then throw (.invalid "empty expected alternatives")
    return .either (← choices.mapM expected)
  | .list (.atom "v128.const" :: .atom shape :: lanes) => do
    if shape == "f32x4" || shape == "f64x2" then
      let width := if shape == "f32x4" then NumWidth.w32 else .w64
      if lanes.length != 128 / width.bits then throw (.invalid "incorrect expected lane count")
      return .vector width (← lanes.mapM fun lane =>
        expected (.list [.atom (if width == .w32 then "f32.const" else "f64.const"), lane]))
    else return .value (← vectorLiteral shape lanes)
  | .list [.atom "f32.const", .atom "nan:canonical"] => .ok (.nan .w32 true)
  | .list [.atom "f64.const", .atom "nan:canonical"] => .ok (.nan .w64 true)
  | .list [.atom "f32.const", .atom "nan:arithmetic"] => .ok (.nan .w32 false)
  | .list [.atom "f64.const", .atom "nan:arithmetic"] => .ok (.nan .w64 false)
  | .list [.atom "ref.null"] => .ok .null
  | expr@(.list [.atom "ref.null", .atom _]) => do
    let _ ← constant expr
    return .null
  | .list [.atom "ref.eq"] => .ok .eq
  | .list [.atom "ref.any"] => .ok .any
  | .list [.atom "ref.struct"] => .ok .struct_
  | .list [.atom "ref.array"] => .ok .array
  | .list [.atom "ref.i31"] => .ok .i31
  | .list [.atom "ref.func"] => .ok .func
  | .list [.atom "ref.extern"] => .ok .extern
  | expr => do return .value (← constant expr)

private partial def Expected.matches : Expected → Value → Bool
  | .either choices, actual => choices.any (fun choice => choice.matches actual)
  | .vector width lanes, .v128 bits =>
    (lanes.zipIdx).all fun (wanted, i) =>
      wanted.matches (floatValue width (vectorLane width.bits bits.toNat i))
  | .value wanted, actual => wanted == actual
  | .null, .ref (.null _) => true
  | .func, .ref (.func _) => true
  | .eq, .ref (.i31 _) | .eq, .ref (.struct_ _) | .eq, .ref (.array _) => true
  | .any, .ref (.i31 _) | .any, .ref (.struct_ _) | .any, .ref (.array _) |
      .any, .ref (.host _) => true
  | .struct_, .ref (.struct_ _) => true
  | .array, .ref (.array _) => true
  | .i31, .ref (.i31 _) => true
  | .extern, .ref (.extern _) | .extern, .ref (.external _) => true
  | .nan width canonical, actual => match floatBits? width actual with
    | none => false
    | some bits => if canonical then floatIsCanonicalNaN width bits
      else floatIsArithmeticNaN width bits
  | _, _ => false

private def instantiateDefinition (fuel callDepth : Nat) (state : State) (source : ValidatedModule)
    (id : Option String) : State × Outcome :=
  let attempted : Result Native.InstantiationResult := do
    let addresses ← linkImports state source.val
    match Native.instantiate fuel state.store source addresses callDepth with
    | .ok result => return result
    | .error .allocation | .error .resourceLimit =>
      throw (.unsupported "instantiation allocation budget")
    | .error e => throw (.invalid s!"instantiation: {repr e}")
  let (next, current, outcome) := match attempted with
    | .error e => (state, none, fromError e)
    | .ok result =>
      let execution := result.execution
      let next := {state with
        store := execution.state.store
        output := state.output ++ execution.output}
      match execution.status with
      | .finished [] => (next, some execution.state.frame.module, .passed)
      | status => (next, none, .failed s!"module initialization: {repr status}")
  let named := match id with
    | some id => (id, current) :: next.named.filter (fun p => p.1 != id)
    | none => next.named
  ({next with current, named}, outcome)

private def rememberDefinition (state : State) (id : Option String)
    (source : Option ValidatedModule) : State :=
  let definitions := match id with
    | some id => (id, source) :: state.definitions.filter (fun p => p.1 != id)
    | none => state.definitions
  {state with definition := source, definitions}

private def selectDefinition (state : State) (fields : List SExpr) :
    Result (Option String × ValidatedModule) := do
  let (id, selected) ← match fields with
    | [] => pure (none, none)
    | [.atom source] =>
      if !source.startsWith "$" then throw (.invalid "module instance requires identifiers")
      pure (none, some source)
    | [.atom id, .atom source] =>
      if !id.startsWith "$" || !source.startsWith "$" then
        throw (.invalid "module instance requires identifiers")
      pure (some id, some source)
    | _ => throw (.invalid "module instance syntax")
  let source ← match selected with
    | none => pure state.definition
    | some name => match state.definitions.lookup name with
      | some source => pure source
      | none => throw (.invalid s!"unknown module definition {name}")
  let some source := source | throw (.unsupported "module definition unavailable")
  return (id, source)

private def assertionSource (state : State) (source : SExpr) : Result ValidatedModule :=
  match source with
  | .list (.atom "module" :: .atom "instance" :: fields) =>
    (selectDefinition state fields).map Prod.snd
  | _ => validateSource source

private def command (fuel callDepth : Nat) (state : State) (expr : SExpr) :
    State × Outcome := Id.run do
  match expr with
  | .list (.atom "module" :: .atom "definition" :: fields) =>
    let source := SExpr.list (.atom "module" :: fields)
    let id := moduleName source
    match validateSource source with
    | .ok validated => return (rememberDefinition state id (some validated), .passed)
    | .error e => return (rememberDefinition state id none, fromError e)
  | .list (.atom "module" :: .atom "instance" :: fields) =>
    let attempted := selectDefinition state fields
    match attempted with
    | .ok (id, source) => return instantiateDefinition fuel callDepth state source id
    | .error e =>
      let named := match fields with
        | [.atom id, .atom _] =>
          if id.startsWith "$" then
            (id, none) :: state.named.filter (fun p => p.1 != id)
          else state.named
        | _ => state.named
      return ({state with current := none, named}, fromError e)
  | .list (.atom "module" :: _) =>
    let id := moduleName expr
    match validateSource expr with
    | .ok source =>
      let remembered := rememberDefinition state id (some source)
      return instantiateDefinition fuel callDepth remembered source id
    | .error e =>
      let next := rememberDefinition state id none
      let named := match id with
        | some id => (id, none) :: next.named.filter (fun p => p.1 != id)
        | none => next.named
      return ({next with current := none, named}, fromError e)
  | .list (.atom "register" :: .string bytes :: fields) =>
    let attempted : Result (String × Option ModuleInst × Outcome) := do
      let registration ← name bytes
      let id ← match fields with
        | [] => pure none
        | [.atom id] => pure (some id)
        | _ => throw (.invalid "register syntax")
      match owner state id with
      | .ok provider => return (registration, some provider, .passed)
      | .error (.unsupported msg) => return (registration, none, .unsupported msg)
      | .error e => throw e
    match attempted with
    | .ok (registration, provider, outcome) =>
      return ({state with registered := (registration, provider) ::
        state.registered.filter (fun p => p.1 != registration)}, outcome)
    | .error e => return (state, fromError e)
  | .list [.atom "assert_unlinkable", source, .string _] =>
    match assertionSource state source with
    | .error e => return (state, fromError e)
    | .ok validated => match linkImports state validated.val with
      | .error (.invalid _) => return (state, .passed)
      | .error (.unsupported msg) => return (state, .unsupported msg)
      | .ok _ => return (state, .failed "expected unlinkable module, linking succeeded")
  | .list [.atom "assert_malformed", source, .string _] =>
    match decodeModule source with
    | .error (.invalid _) => return (state, .passed)
    | .error (.unsupported msg) => return (state, .unsupported msg)
    | .ok _ => return (state, .failed "expected malformed module, decoding succeeded")
  | .list [.atom "assert_invalid", source, .string _] =>
    match decodeModule source with
    | .error (.unsupported msg) => return (state, .unsupported msg)
    | .error (.invalid msg) =>
      return (state, .failed s!"module elaboration failed before validation: {msg}")
    | .ok source => match Validation.validate source with
      | .ok () => return (state, .failed "expected invalid module, validation succeeded")
      | .error (.invalid _) => return (state, .passed)
      | .error (.unsupported msg) => return (state, .unsupported s!"validation: {msg}")
  | .list (.atom "assert_return" :: action :: expected) =>
    match expected.mapM Wasm.Text.expected with
    | .error e => return (state, fromError e)
    | .ok vs => match Wasm.Text.action fuel callDepth state action with
      | .error e => return (state, fromError e)
      | .ok (next, .finished actual) =>
        let matched := actual.length == vs.length &&
          (vs.zip actual).all (fun (e, v) => e.matches v)
        return (next, if matched then .passed
          else .failed s!"expected {repr vs}, got {repr actual}")
      | .ok (next, status) => return (next, .failed s!"expected return, got {repr status}")
  | .list [.atom "assert_trap", source@(.list (.atom "module" :: _)), .string _] =>
    let attempted : Result Native.InstantiationResult := do
      let validated ← assertionSource state source
      let addresses ← linkImports state validated.val
      match Native.instantiate fuel state.store validated addresses callDepth with
      | .ok result => return result
      | .error .allocation => throw (.unsupported "instantiation allocation budget")
      | .error e => throw (.invalid s!"instantiation: {repr e}")
    match attempted with
    | .error e => return (state, fromError e)
    | .ok result =>
      let next := {state with
        store := result.execution.state.store
        output := state.output ++ result.execution.output}
      match result.execution.status with
      | .trapped => return (next, .passed)
      | status => return (next, .failed s!"expected initialization trap, got {repr status}")
  | .list [.atom "assert_exception", action] =>
    match Wasm.Text.action fuel callDepth state action with
    | .error e => return (state, fromError e)
    | .ok (next, .exception _) => return (next, .passed)
    | .ok (next, status) =>
      return (next, .failed s!"expected exception, got {repr status}")
  | .list [.atom "assert_exhaustion", action, .string _] =>
    match Wasm.Text.action fuel callDepth state action with
    | .error e => return (state, fromError e)
    | .ok (next, .callStackExhausted) => return (next, .passed)
    | .ok (next, status) =>
      return (next, .failed s!"expected call-stack exhaustion, got {repr status}")
  | .list [.atom "assert_trap", action, .string _] =>
    match Wasm.Text.action fuel callDepth state action with
    | .error e => return (state, fromError e)
    | .ok (next, .trapped) => return (next, .passed)
    | .ok (next, status) => return (next, .failed s!"expected trap, got {repr status}")
  | .list (.atom "invoke" :: _) | .list (.atom "get" :: _) =>
    match action fuel callDepth state expr with
    | .error e => return (state, fromError e)
    | .ok (next, .finished _) => return (next, .passed)
    | .ok (next, status) => return (next, .failed s!"action: {repr status}")
  | .list (.atom tag :: _) => return (state, .unsupported s!"script command {tag}")
  | _ => return (state, .failed "expected script command")

/-- Execute supported scripts; module instantiation uses `Validation.validate_sound`. -/
def runScript (commands : List SExpr) (fuel : Nat := 10000)
    (callDepth : Nat := 1024) : Report := Id.run do
  let commands := if !commands.isEmpty && commands.all (fun
      | .list (.atom field :: _) =>
        ["type", "rec", "import", "func", "global", "memory", "table", "tag",
          "export", "start", "elem", "data"].contains field
      | _ => false) then [.list (.atom "module" :: commands)] else commands
  let mut state : State := {}
  let mut report : Report := {}
  for expr in commands do
    let (next, outcome) := command fuel callDepth state expr
    state := next
    report := {outcomes := report.outcomes ++ [outcome]}
  return {report with output := state.output}

end Wasm.Text
