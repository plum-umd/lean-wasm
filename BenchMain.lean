import Wasm.NativeExecution
import Wasm.Fast.DepthWorkloads

open Wasm

@[noinline] private def evaluate {α : Type} (action : Unit → α) : IO α :=
  pure (action ())

private def sample (backend kind : String) (iterations depth : Nat) : IO Unit := do
  let nested := Wasm.Fast.DepthWorkloads.kinds.contains kind
  let input ← evaluate fun _ => if nested then
    Wasm.Fast.DepthWorkloads.configuration kind iterations depth
    else Wasm.Fast.Workloads.configuration kind iterations
  let fuel := if nested then Wasm.Fast.DepthWorkloads.fuel iterations depth
    else Wasm.Fast.Workloads.fuel kind iterations
  let expected := if nested then Wasm.Fast.DepthWorkloads.expected kind iterations
    else RunStatus.finished (Wasm.Fast.Workloads.expected kind iterations)
  let begin ← IO.monoNanosNow
  let machine ← evaluate fun _ =>
    Wasm.Fast.Machine.ofConfiguration (Wasm.Fast.Configuration.ofSpec input)
  let ready ← IO.monoNanosNow
  let (final, status) ← evaluate fun _ => if backend == "native" then
    let result := Wasm.Native.runMachine fuel machine
    (result.state, result.status)
    else
      let result := Wasm.Fast.Machine.run fuel machine
      (result.state, result.status)
  let stop ← IO.monoNanosNow
  let state ← evaluate fun _ => final.toSpec
  let decoded ← IO.monoNanosNow
  let execution := stop - ready
  let inbound := ready - begin
  let outbound := decoded - stop
  unless status == expected do
    throw (IO.userError s!"{backend}/{kind}/{iterations}/{depth}: unexpected {repr status}")
  let heapSize := if nested || kind == "control" then 0 else iterations
  unless state.store.structs.length == heapSize do throw (IO.userError "wrong heap size")
  let exceptions := if kind == "unwind" then 1 else 0
  unless state.store.exns.length == exceptions do throw (IO.userError "wrong exception count")
  IO.println (s!"{backend},{kind},{iterations},{depth},{fuel},{execution}," ++
    s!"{inbound},{outbound},{heapSize}")

def main (args : List String) : IO UInt32 := do
  match args with
  | [backend, kind, count, nesting] =>
    unless ["certified", "native"].contains backend do
      throw (IO.userError "mode must be certified or native")
    unless (Wasm.Fast.DepthWorkloads.kinds ++ ["allocate", "allocate-read", "linked",
      "read-early", "read-middle", "read-late", "control"]).contains kind do
      throw (IO.userError "unknown workload")
    let some iterations := count.toNat? | throw (IO.userError "invalid iteration count")
    let some depth := nesting.toNat? | throw (IO.userError "invalid depth")
    unless iterations > 0 && iterations ≤ 1000000 && depth ≤ 512 do
      throw (IO.userError "iterations must be in 1..1000000 and depth in 0..512")
    sample backend kind iterations depth
    return 0
  | _ =>
    IO.eprintln "usage: lake exe wasm-bench certified|native WORKLOAD ITERATIONS DEPTH"
    return 1
