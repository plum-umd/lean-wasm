import Wasm.NativeVector
import Wasm.Spectest
import Wasm.NativeFloat
import Wasm.Instantiation

/-! Optional execution backend with unproved native float arithmetic and spectest host calls.
Native steps fall back to certified execution and propagate its resource-limit classification.
This backend deliberately provides no `ConfigStep`/`ConfigSteps` soundness theorem. -/
namespace Wasm.Native

private def arity : Instr → Option Nat
  | .vector op => some op.opcode.signature.params.length
  | .floatUnary _ _ | .floatConvert _ => some 1
  | .floatBinary _ _ | .floatRel _ _ => some 2
  | _ => none

private def redex (instr : Instr) (args : List Value) : Option (List AdminInstr) := do
  match instr, args with
  | .vector op, args => return values [← evalNativeVector op args]
  | .floatUnary width op, [a] => return values [← evalUnary width op a]
  | .floatBinary width op, [a, b] => return values [← evalBinary width op a b]
  | .floatRel width op, [a, b] => return values [← evalRel width op a b]
  | .floatConvert op, [a] =>
    match ← evalConvert op a with
    | none => return [.trap]
    | some value => return values [value]
  | _, _ => none

private def splitNativeValues : List AdminInstr → List Value × List AdminInstr
  | .instr (.const v) :: tail =>
    let (vs, rest) := splitNativeValues tail
    (v :: vs, rest)
  | es => ([], es)

private partial def nativeStep (store : Store) (frame : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := do
  let (vs, rest) := splitNativeValues code
  match rest with
  | .instr instr :: tail =>
    let n ← arity instr
    if vs.length < n then none else do
      let result ← redex instr (vs.drop (vs.length - n))
      return (store, values (vs.take (vs.length - n)) ++ result ++ tail)
  | .returnInvokeRef type :: tail =>
    let .ref (.func address) :: operands := vs.reverse | none
    let function ← store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.definedType.heap
    if !Spectest.accepts function then none else
      return (store, values operands.reverse ++ [.returnInvoke address function.type] ++ tail)
  | .returnInvokeDefined type :: tail =>
    let .ref (.func address) :: operands := vs.reverse | none
    let function ← store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.heap
    if !Spectest.accepts function then none else
      return (store, values operands.reverse ++ [.returnInvoke address function.type] ++ tail)
  | .returnInvoke address type :: tail =>
    let function ← store.func? address
    if function.type != type || !Spectest.accepts function then none else do
      let n := type.params.length
      if vs.length < n then none else do
        let _ ← checkArgs store (vs.drop (vs.length - n)) type.params
        return (store, values (vs.take (vs.length - n)) ++ [.tailActivation []] ++ tail)
  | .invokeRef type :: tail =>
    let .ref (.func address) :: operands := vs.reverse | none
    let function ← store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.definedType.heap
    if !Spectest.accepts function then none else
      return (store, values operands.reverse ++ [.invoke address function.type] ++ tail)
  | .invokeDefined type :: tail =>
    let .ref (.func address) :: operands := vs.reverse | none
    let function ← store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.heap
    if !Spectest.accepts function then none else
      return (store, values operands.reverse ++ [.invoke address function.type] ++ tail)
  | .invoke address type :: tail =>
    let function ← store.func? address
    if function.type != type || !Spectest.accepts function then none else do
      let n := type.params.length
      if vs.length < n then none else do
        let _ ← checkArgs store (vs.drop (vs.length - n)) type.params
        return (store, values (vs.take (vs.length - n)) ++ tail)
  | .handler catches body :: tail =>
    let (store, body) ← nativeStep store frame body
    return (store, values vs ++ [.handler catches body] ++ tail)
  | .label n continuation body :: tail =>
    let (store, body) ← nativeStep store frame body
    return (store, values vs ++ [.label n continuation body] ++ tail)
  | .frame n inner body :: tail =>
    let (store, body) ← nativeStep store inner body
    return (store, values vs ++ [.frame n inner body] ++ tail)
  | _ => none

/-- Certified reductions take precedence; native float and host calls extend their domain. -/
def step (config : Configuration) : Option Configuration :=
  (stepConfiguration config).orElse fun _ =>
    (nativeStep config.store config.frame config.code).map fun next =>
      {config with store := next.1, code := next.2}

private partial def hostOutput (store : Store) (code : List AdminInstr) : List Value :=
  let (vs, rest) := splitNativeValues code
  match rest with
  | .invoke address _ :: _ | .returnInvoke address _ :: _ => match store.func? address with
    | some function => if Spectest.accepts function then
        vs.drop (vs.length - function.type.params.length) else []
    | none => []
  | .label _ _ body :: _ | .frame _ _ body :: _ | .handler _ body :: _ => hostOutput store body
  | _ => []

structure RunResult extends ConfigurationRunResult where
  output : List Value := []

private def canActivate (store : Store) (function : FuncInst) (vs : List Value) : Bool :=
  let n := function.type.params.length
  if vs.length < n then false else
    let args := vs.drop (vs.length - n)
    match function.code with
    | .wasm _ => (function.activation? args store).isSome
    | .host _ | .hostTyped _ _ =>
      Spectest.accepts function && (checkArgs store args function.type.params).isSome

/-- Count active function frames along the current evaluation context only.
Labels and suspended continuations do not contribute to the call depth. -/
private partial def exceedsCallDepth (store : Store) (limit depth : Nat)
    (code : List AdminInstr) : Bool :=
  let (vs, rest) := splitNativeValues code
  match rest with
  | .invokeRef type :: _ =>
    match vs.getLast? with
    | some (.ref (.func address)) => match store.func? address with
      | some function =>
        depth ≥ limit &&
          (checkRuntimeHeap function.runtimeType.heap type.definedType.heap).isSome &&
          canActivate store function (vs.take (vs.length - 1))
      | none => false
    | _ => false
  | .invokeDefined type :: _ =>
    match vs.getLast? with
    | some (.ref (.func address)) => match store.func? address with
      | some function =>
        depth ≥ limit && (checkRuntimeHeap function.runtimeType.heap type.heap).isSome &&
          canActivate store function (vs.take (vs.length - 1))
      | none => false
    | _ => false
  | .invoke address type :: _ =>
    match store.func? address with
    | some function => depth ≥ limit && function.type == type && canActivate store function vs
    | none => false
  | .handler _ body :: _ => exceedsCallDepth store limit depth body
  | .label _ _ body :: _ => exceedsCallDepth store limit depth body
  | .frame _ _ body :: _ => exceedsCallDepth store limit (depth + 1) body
  | _ => false

private def runSteps (callDepth : Nat) :
    Nat → Configuration → List Value → Configuration × List Value × Bool
  | 0, config, output => (config, output, false)
  | fuel + 1, config, output =>
    if exceedsCallDepth config.store callDepth 0 config.code then (config, output, true)
    else match step config with
      | none => (config, output, false)
      | some next => runSteps callDepth fuel next
          (output ++ hostOutput config.store config.code)

/-- Native execution records spectest output and limits function activation depth.
Fuel exhaustion remains distinct from call-stack and allocation resource exhaustion. -/
def run (fuel : Nat) (config : Configuration) (callDepth : Nat := 1024) : RunResult :=
  let (final, output, depthExhausted) := runSteps callDepth fuel config []
  let status := if depthExhausted then RunStatus.callStackExhausted else
    match step final with
    | some _ => RunStatus.exhausted
    | none => match stepConfigurationOutcome final with
      | .next _ => .exhausted
      | .stopped status => status
  { state := final, status, output }

structure InstantiationResult where
  execution : RunResult

/-- Source validation and allocation remain certified; initialization uses native execution. -/
def instantiate (fuel : Nat) (store : Store) (module : ValidatedModule)
    (addresses : List ExternAddr) (callDepth : Nat := 1024) :
    Except InstantiationError InstantiationResult := do
  let prepared ← checkedPrepareInstantiation store module.val addresses
  return ⟨run fuel prepared.val callDepth⟩

end Wasm.Native
