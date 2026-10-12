import Wasm.NativeVector
import Wasm.Spectest
import Wasm.NativeFloat
import Wasm.Instantiation

/-! Native float arithmetic and spectest host calls extend the explicit execution machine.
The certified APIs retain their reduction soundness proofs; these native extensions are
unproved and do not claim `ConfigStep`/`ConfigSteps` soundness. -/
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

private def nativeChange (m : Execution.Machine) : Option Execution.Machine.PlannedStep := do
  let head :: tail := m.code | none
  let next (code : List AdminInstr) (operands : List Value) (output : List Value := []) :=
    some (⟨⟨{m with code := code ++ tail, operands}, .unchanged⟩, output⟩ :
      Execution.Machine.PlannedStep)
  match head with
  | .instr instr =>
    let n ← arity instr
    let args := m.operands.take n
    if args.length != n then none else do
      let result ← redex instr args.reverse
      next result (m.operands.drop n)
  | .invokeRef type | .returnInvokeRef type =>
    let .ref (.func address) :: operands := m.operands | none
    let function ← m.store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.definedType.heap
    if !Spectest.accepts function then none else
      next [if head matches .returnInvokeRef _ then .returnInvoke address function.type
        else .invoke address function.type] operands
  | .invokeDefined type | .returnInvokeDefined type =>
    let .ref (.func address) :: operands := m.operands | none
    let function ← m.store.func? address
    let _ ← checkRuntimeHeap function.runtimeType.heap type.heap
    if !Spectest.accepts function then none else
      next [if head matches .returnInvokeDefined _ then .returnInvoke address function.type
        else .invoke address function.type] operands
  | .invoke address type | .returnInvoke address type =>
    let function ← m.store.func? address
    if function.type != type || !Spectest.accepts function then none else do
      let n := type.params.length
      let args := m.operands.take n
      if args.length != n then none else do
        let _ ← Execution.checkArgs m.store args.reverse type.params
        let code := if head matches .returnInvoke _ _ then [.tailActivation []] else []
        next code (m.operands.drop n) args.reverse
  | _ => none

private def canActivate (store : Execution.Store) (function : FuncInst)
    (operands : List Value) : Bool :=
  let n := function.type.params.length
  let args := operands.take n
  if args.length != n then false else
    match function.code with
    | .wasm _ => (Execution.FuncInst.activation? function args.reverse store).isSome
    | .host _ | .hostTyped _ _ =>
      Spectest.accepts function && (Execution.checkArgs store args.reverse function.type.params).isSome

-- Count suspended calls only when an instruction can activate a function. Ordinary
-- instructions do not traverse the context stack for resource checks.
private def exceedsCallDepth (limit : Nat) (m : Execution.Machine) : Bool :=
  let atLimit := fun _ : Unit =>
    m.contexts.foldl (fun depth context => match context.kind with
      | .call _ _ => depth + 1 | _ => depth) 0 ≥ limit
  match m.code.head? with
  | some (.invokeRef type) =>
    match m.operands with
    | .ref (.func address) :: operands => match m.store.func? address with
      | some function => atLimit () &&
        (checkRuntimeHeap function.runtimeType.heap type.definedType.heap).isSome &&
          canActivate m.store function operands
      | none => false
    | _ => false
  | some (.invokeDefined type) =>
    match m.operands with
    | .ref (.func address) :: operands => match m.store.func? address with
      | some function => atLimit () &&
        (checkRuntimeHeap function.runtimeType.heap type.heap).isSome &&
          canActivate m.store function operands
      | none => false
    | _ => false
  | some (.invoke address type) =>
    match m.store.func? address with
    | some function => atLimit () && function.type == type &&
        canActivate m.store function m.operands
    | none => false
  | _ => false

private def hooks (callDepth : Nat) : Execution.Machine.ExecutionHooks :=
  ⟨nativeChange, exceedsCallDepth callDepth⟩

/-- Certified reductions take precedence; native float and host calls extend their domain. -/
def step (config : Configuration) : Option Configuration :=
  let m := Execution.Machine.normalize
    (Execution.Machine.ofConfiguration (Execution.Configuration.ofSpec config))
  (Execution.Machine.planWith (hooks 1024) m).map fun plan => plan.change.commit.toSpec

structure RunResult extends ConfigurationRunResult where
  output : List Value := []

structure MachineRunResult extends Execution.Machine.RunResult where
  output : List Value := []

-- Embedders can retain this state across runs without decoding the heap or contexts.
def runMachine (fuel : Nat) (m : Execution.Machine) (callDepth : Nat := 1024) : MachineRunResult :=
  let result := Execution.Machine.execute (hooks callDepth) fuel m []
  let focused := Execution.Machine.normalize result.state
  let status := if result.limitExceeded then RunStatus.callStackExhausted else
    if (Execution.Machine.planWith (hooks callDepth) focused).isSome then .exhausted
    else Execution.Machine.terminalStatus focused
  {state := result.state, status, output := result.output}

/-- Native execution records spectest output and limits function activation depth.
Fuel exhaustion remains distinct from call-stack resource exhaustion. -/
def run (fuel : Nat) (config : Configuration) (callDepth : Nat := 1024) : RunResult :=
  let result := runMachine fuel
    (Execution.Machine.ofConfiguration (Execution.Configuration.ofSpec config)) callDepth
  {state := result.state.toSpec, status := result.status, output := result.output}

structure InstantiationResult where
  execution : RunResult

/-- Source validation and allocation remain certified; initialization uses native execution. -/
def instantiate (fuel : Nat) (store : Store) (module : ValidatedModule)
    (addresses : List ExternAddr) (callDepth : Nat := 1024) :
    Except InstantiationError InstantiationResult := do
  let prepared ← checkedPrepareInstantiation store module.val addresses
  return ⟨run fuel prepared.val callDepth⟩

end Wasm.Native
