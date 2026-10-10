import Wasm.Text.Module
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
  if decide (ImportsMatch state.store source.types source.imports addresses
      (source.resolvedTypes?.getD [])) then return addresses
  else throw (.invalid "import types do not match")

private def validateSource (expr : SExpr) : Result ValidatedModule := do
  let source ← module expr
  match hv : Validation.validate source with
  | .ok () => return ⟨source, Validation.validate_sound hv⟩
  | .error (.invalid msg) => throw (.invalid s!"validation: {msg}")
  | .error (.unsupported msg) => throw (.unsupported s!"validation: {msg}")

private def invoke (fuel : Nat) (state : State) (expr : SExpr) :
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
  let vs ← args.mapM constant
  let some _ := checkArgs state.store vs f.type.params |
    throw (.invalid "function arguments do not match")
  let activation := values vs ++ [.invoke address f.type]
  let execution := Native.run fuel ⟨state.store, ⟨[], m⟩, activation⟩
  return ({state with
    store := execution.state.store
    output := state.output ++ execution.output}, execution.status)

private def action (fuel : Nat) (state : State) (expr : SExpr) :
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
  | _ => invoke fuel state expr

private inductive Expected where
  | value (value : Value)
  | null
  | func
  | extern
  | nan (width : NumWidth) (canonical : Bool)
  deriving Repr

private def expected : SExpr → Result Expected
  | .list [.atom "f32.const", .atom "nan:canonical"] => .ok (.nan .w32 true)
  | .list [.atom "f64.const", .atom "nan:canonical"] => .ok (.nan .w64 true)
  | .list [.atom "f32.const", .atom "nan:arithmetic"] => .ok (.nan .w32 false)
  | .list [.atom "f64.const", .atom "nan:arithmetic"] => .ok (.nan .w64 false)
  | .list [.atom "ref.null"] => .ok .null
  | .list [.atom "ref.func"] => .ok .func
  | .list [.atom "ref.extern"] => .ok .extern
  | expr => do return .value (← constant expr)

private def Expected.matches : Expected → Value → Bool
  | .value wanted, actual => wanted == actual
  | .null, .ref (.null _) => true
  | .func, .ref (.func _) => true
  | .extern, .ref (.extern _) => true
  | .nan width canonical, actual => match floatBits? width actual with
    | none => false
    | some bits => if canonical then floatIsCanonicalNaN width bits
      else floatIsArithmeticNaN width bits
  | _, _ => false

private def command (fuel : Nat) (state : State) (expr : SExpr) : State × Outcome := Id.run do
  match expr with
  | .list (.atom "module" :: _) =>
    -- Always replace the current module, even when unsupported: never reuse a stale instance.
    let attempted : Result (Store × ModuleInst × List Value) := do
      let validated ← validateSource expr
      let addresses ← linkImports state validated.val
      let result ← match Native.instantiate fuel state.store validated addresses with
        | .ok result => .ok result
        | .error .allocation => .error (.unsupported "instantiation allocation budget")
        | .error e => .error (.invalid s!"instantiation: {repr e}")
      let execution := result.execution
      match execution.status with
      | .finished [] => return (execution.state.store, execution.state.frame.module, execution.output)
      | _ => throw (.invalid s!"module initialization: {repr execution.status}")
    let (store, current, output, outcome) := match attempted with
      | .ok (s, m, printed) => (s, some m, state.output ++ printed, .passed)
      | .error e => (state.store, none, state.output, fromError e)
    let named := match moduleName expr with
      | some id => (id, current) :: state.named.filter (fun p => p.1 != id)
      | none => state.named
    return ({state with store, current, named, output}, outcome)
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
    match validateSource source with
    | .error e => return (state, fromError e)
    | .ok validated => match linkImports state validated.val with
      | .error (.invalid _) => return (state, .passed)
      | .error (.unsupported msg) => return (state, .unsupported msg)
      | .ok _ => return (state, .failed "expected unlinkable module, linking succeeded")
  | .list [.atom "assert_invalid", source, .string _] =>
    match module source with
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
    | .ok vs => match Wasm.Text.action fuel state action with
      | .error e => return (state, fromError e)
      | .ok (next, .finished actual) =>
        let matched := actual.length == vs.length &&
          (vs.zip actual).all (fun (e, v) => e.matches v)
        return (next, if matched then .passed
          else .failed s!"expected {repr vs}, got {repr actual}")
      | .ok (next, status) => return (next, .failed s!"expected return, got {repr status}")
  | .list [.atom "assert_trap", source@(.list (.atom "module" :: _)), .string _] =>
    let attempted : Result Native.InstantiationResult := do
      let validated ← validateSource source
      let addresses ← linkImports state validated.val
      match Native.instantiate fuel state.store validated addresses with
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
  | .list [.atom "assert_trap", action, .string _] =>
    match Wasm.Text.action fuel state action with
    | .error e => return (state, fromError e)
    | .ok (next, .trapped) => return (next, .passed)
    | .ok (next, status) => return (next, .failed s!"expected trap, got {repr status}")
  | .list (.atom "invoke" :: _) | .list (.atom "get" :: _) =>
    match action fuel state expr with
    | .error e => return (state, fromError e)
    | .ok (next, .finished _) => return (next, .passed)
    | .ok (next, status) => return (next, .failed s!"action: {repr status}")
  | .list (.atom tag :: _) => return (state, .unsupported s!"script command {tag}")
  | _ => return (state, .failed "expected script command")

/-- Execute supported scripts; module instantiation uses `Validation.validate_sound`. -/
def runScript (commands : List SExpr) (fuel : Nat := 10000) : Report := Id.run do
  let mut state : State := {}
  let mut report : Report := {}
  for expr in commands do
    let (next, outcome) := command fuel state expr
    state := next
    report := {outcomes := report.outcomes ++ [outcome]}
  return {report with output := state.output}

end Wasm.Text
