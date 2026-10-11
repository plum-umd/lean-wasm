import Wasm.Fast.Workloads

open Wasm
open Wasm.Fast.Workloads

@[noinline] private def allocateSpec (n : Nat) : Wasm.Store := Id.run do
  let mut store : Wasm.Store := {}
  for i in [:n] do
    store := (store.allocateStruct (object i)).2
  return store

@[noinline] private def allocateFast (n : Nat) : Wasm.Fast.Store := Id.run do
  let mut store : Wasm.Fast.Store := {}
  for i in [:n] do
    store := (store.allocateStruct (object i)).2
  return store

@[noinline] private def lookupSpec (store : Wasm.Store) (address count : Nat) : Nat := Id.run do
  let mut sum := 0
  for _ in [:count] do
    if let some object := store.struct? ⟨address⟩ then sum := sum + object.fields.length
  return sum

@[noinline] private def lookupFast (store : Wasm.Fast.Store)
    (address count : Nat) : Nat := Id.run do
  let mut sum := 0
  for _ in [:count] do
    if let some object := store.struct? ⟨address⟩ then sum := sum + object.fields.length
  return sum

-- IO sequencing prevents Lean's pure-let scheduling from moving work across timer reads.
@[noinline] private def evaluate {α : Type} (action : Unit → α) : IO α :=
  pure (action ())

private def verify (kind : String) (n : Nat) (state : Wasm.Configuration)
    (status : RunStatus) : IO Unit := do
  unless status == .finished (expected kind n) do
    throw (IO.userError s!"{kind}/{n}: unexpected status {repr status}")
  let expectedHeap := if kind == "control" then 0 else n
  unless state.store.structs.length == expectedHeap do
    throw (IO.userError s!"{kind}/{n}: wrong heap size")

-- Each process has fresh inputs. Setup, conversion and verification have separate timings.
private def sample (backend kind : String) (n : Nat) : IO Unit := do
  if kind == "heap-allocate" then
    let start ← IO.monoNanosNow
    let checksum ← if backend == "fast" then do
      let store ← evaluate fun _ => allocateFast n
      let stop ← IO.monoNanosNow
      IO.println s!"{backend},{kind},{n},0,{stop - start},0,0,{store.structs.size}"
      pure store.structs.size
    else do
      let store ← evaluate fun _ => allocateSpec n
      let stop ← IO.monoNanosNow
      IO.println s!"{backend},{kind},{n},0,{stop - start},0,0,{store.structs.length}"
      pure store.structs.length
    unless checksum == n do throw (IO.userError "allocation checksum mismatch")
    return
  if kind.startsWith "heap-read-" then
    let store ← evaluate fun _ => ({structs := (List.range n).map object} : Wasm.Store)
    let address := if kind == "heap-read-early" then 0
      else if kind == "heap-read-middle" then n / 2 else n - 1
    if backend == "fast" then
      let fast ← evaluate fun _ => Wasm.Fast.Store.ofSpec store
      let start ← IO.monoNanosNow
      let checksum ← evaluate fun _ => lookupFast fast address n
      let stop ← IO.monoNanosNow
      unless checksum == n do throw (IO.userError "lookup checksum mismatch")
      IO.println s!"{backend},{kind},{n},0,{stop - start},0,0,{n}"
    else
      let start ← IO.monoNanosNow
      let checksum ← evaluate fun _ => lookupSpec store address n
      let stop ← IO.monoNanosNow
      unless checksum == n do throw (IO.userError "lookup checksum mismatch")
      IO.println s!"{backend},{kind},{n},0,{stop - start},0,0,{n}"
    return
  let input ← evaluate fun _ => configuration kind n
  let limit := fuel kind n
  let begin ← IO.monoNanosNow
  if backend == "fast" then
    let fast ← evaluate fun _ => Wasm.Fast.Configuration.ofSpec input
    let ready ← IO.monoNanosNow
    let result ← evaluate fun _ => Wasm.Fast.runConfiguration limit fast
    let done ← IO.monoNanosNow
    let decoded ← evaluate fun _ => result.state.toSpec
    let converted ← IO.monoNanosNow
    verify kind n decoded result.status
    IO.println (s!"{backend},{kind},{n},{limit},{done - ready},{ready - begin}," ++
      s!"{converted - done},{decoded.store.structs.length}")
  else
    let result ← evaluate fun _ => Wasm.runConfiguration limit input
    let done ← IO.monoNanosNow
    verify kind n result.state result.status
    IO.println (s!"{backend},{kind},{n},{limit},{done - begin},0,0," ++
      s!"{result.state.store.structs.length}")

def main (args : List String) : IO UInt32 := do
  match args with
  | [backend, kind, size] =>
    unless backend == "spec" || backend == "fast" do
      throw (IO.userError "backend must be spec or fast")
    let some n := size.toNat? | throw (IO.userError "size must be a natural number")
    unless n > 0 && n ≤ 1000000 do throw (IO.userError "size must be in 1..1000000")
    unless ["heap-allocate", "heap-read-early", "heap-read-middle", "heap-read-late",
      "allocate", "allocate-read", "linked", "read-early", "read-middle", "read-late",
      "control"].contains kind do throw (IO.userError "unknown workload")
    sample backend kind n
    return 0
  | _ =>
    IO.eprintln "usage: lake exe wasm-bench spec|fast WORKLOAD SIZE"
    return 1
