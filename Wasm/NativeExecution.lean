import Wasm.Spectest
import Wasm.NativeFloat
import Wasm.Instantiation

/-! Optional execution backend with unproved native float arithmetic and spectest host calls.
The certified `stepConfiguration` and `runConfiguration` APIs are unchanged.
This backend deliberately provides no `ConfigStep`/`ConfigSteps` soundness theorem. -/
namespace Wasm.Native

private def arity : Instr → Option Nat
  | .floatUnary _ _ | .floatConvert _ => some 1
  | .floatBinary _ _ | .floatRel _ _ => some 2
  | _ => none

private def redex (instr : Instr) (args : List Value) : Option (List AdminInstr) := do
  match instr, args with
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
  | .invoke address _ :: _ => match store.func? address with
    | some function => if Spectest.accepts function then
        vs.drop (vs.length - function.type.params.length) else []
    | none => []
  | .label _ _ body :: _ | .frame _ _ body :: _ => hostOutput store body
  | _ => []

structure RunResult extends ConfigurationRunResult where
  output : List Value := []

private def runSteps : Nat → Configuration → List Value → Configuration × List Value
  | 0, config, output => (config, output)
  | fuel + 1, config, output => match step config with
    | none => (config, output)
    | some next => runSteps fuel next (output ++ hostOutput config.store config.code)

/-- Native execution records spectest print values in execution order. -/
def run (fuel : Nat) (config : Configuration) : RunResult :=
  let (final, output) := runSteps fuel config []
  let status := match step final with
    | some _ => RunStatus.exhausted
    | none => match stepOutcome final.frame.module.types final.code with
      | .finished vs => .finished vs | .trapped => .trapped
      | .stuck => .stuck | .next _ => .exhausted
  { state := final, status, output }

structure InstantiationResult where
  execution : RunResult

/-- Source validation and allocation remain certified; initialization uses native execution. -/
def instantiate (fuel : Nat) (store : Store) (module : ValidatedModule)
    (addresses : List ExternAddr) : Except InstantiationError InstantiationResult := do
  let prepared ← checkedPrepareInstantiation store module.val addresses
  return ⟨run fuel prepared.val⟩

end Wasm.Native
