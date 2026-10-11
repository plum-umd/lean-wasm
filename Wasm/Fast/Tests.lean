import Wasm.Fast.Workloads
import Wasm.Text.Module
import Wasm.Instantiation
import Wasm.ExecutableValidationSoundness

namespace Wasm.Fast.Tests

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"fast executor regression: {name}")

private def agreement (name : String) (c : Wasm.Configuration) : IO Unit := do
  let fast := Configuration.ofSpec c
  check (name ++ ": input roundtrip") (fast.toSpec == c)
  for budget in [0, 1, 2, 3, 5, 10, 40, 200, 10000] do
    let a := Wasm.runConfiguration budget c
    let b := runConfiguration budget fast
    check (name ++ s!": state/fuel {budget}") (a.state == b.state.toSpec)
    check (name ++ s!": status/fuel {budget}") (a.status == b.status)
    check (name ++ s!": optional step {budget}")
      (Wasm.stepConfiguration a.state == (stepConfiguration b.state).map Configuration.toSpec)
    let resumed := runConfiguration 10000 b.state
    let expected := Wasm.runConfiguration 10000 a.state
    check (name ++ s!": resume {budget}")
      (resumed.state.toSpec == expected.state && resumed.status == expected.status)

private def prepare (source : String) : Except String Wasm.Configuration := do
  let exprs ← (Text.parse source).mapError id
  let [expr] := exprs | throw "expected one module"
  let module ← (Text.module expr).mapError fun e => s!"{repr e}"
  let validated ← match hv : Validation.validate module with
    | .ok _ => pure (⟨module, Validation.validate_sound hv⟩ : ValidatedModule)
    | .error e => throw s!"validation: {repr e}"
  let instantiated ← (Wasm.instantiate 10000 {} validated []).mapError fun e => s!"{repr e}"
  let some owner := instantiated.module? | throw "module initialization failed"
  let some (.func address) := owner.export? "main" | throw "missing main function"
  let store := instantiated.execution.state.store
  let some function := store.func? address | throw "missing function instance"
  return ⟨store, ⟨[], owner⟩, [.invoke address function.type]⟩

-- Each fixture exercises a distinct certified instruction family and reference-bearing state.
private def fixtures : List (String × String × List Value) := [
  ("packed mutable alias", "(module
    (type $s (struct (field (mut i8)) (field i64)))
    (global $g (ref $s) (struct.new $s (i32.const 0) (i64.const 9)))
    (func (export \"main\") (result i32 i64)
      global.get $g i32.const 255 struct.set $s 0
      global.get $g struct.get_s $s 0 global.get $g struct.get $s 1))",
    [.i32 4294967295, .i64 9]),
  ("default structs", "(module (type $s (struct (field i32) (field anyref)))
    (func (export \"main\") (result i32) struct.new_default $s struct.get $s 0))", [.i32 0]),
  ("table struct references", "(module (type $s (struct (field i32)))
    (table 2 anyref)
    (func (export \"main\") (result i32)
      i32.const 1 i32.const 42 struct.new $s table.set 0
      i32.const 1 table.get 0 ref.cast (ref $s) struct.get $s 0))", [.i32 42]),
  ("array struct references", "(module
    (type $s (struct (field i32))) (type $a (array (mut (ref $s))))
    (func (export \"main\") (result i32)
      i32.const 42 struct.new $s i32.const 2 array.new $a
      i32.const 1 array.get $a struct.get $s 0))", [.i32 42]),
  ("memory and bulk", "(module (memory 1)
    (func (export \"main\") (result i32)
      i32.const 0 i32.const 42 i32.const 4 memory.fill
      i32.const 8 i32.const 0 i32.const 4 memory.copy
      i32.const 8 i32.load8_u))", [.i32 42]),
  ("direct/reference/tail calls", "(module
    (type $s (struct (field i32))) (type $f (func (param (ref $s)) (result i32)))
    (func $get (type $f) local.get 0 struct.get $s 0)
    (elem declare func $get)
    (func $wrapper (type $f) local.get 0 return_call $get)
    (func (export \"main\") (result i32 i32)
      i32.const 7 struct.new $s call $wrapper
      i32.const 9 struct.new $s ref.func $get call_ref $f))", [.i32 7, .i32 9]),
  ("exception struct payload", "(module
    (type $s (struct (field i32))) (tag $e (param (ref $s)))
    (func (export \"main\") (result i32)
      block $out (result (ref $s))
        try_table (catch $e $out)
          i32.const 42 struct.new $s throw $e
        end unreachable
      end struct.get $s 0))", [.i32 42]),
  ("certified SIMD", "(module (memory 1)
    (func (export \"main\") (result i32)
      i32.const 0 v128.const i32x4 1 2 3 4 v128.store
      i32.const 0 v128.load v128.const i32x4 4 3 2 1 i32x4.add i32x4.extract_lane 0))",
    [.i32 5]),
  ("null trap", "(module (type $s (struct (field i32)))
    (func (export \"main\") (result i32) ref.null $s struct.get $s 0))", [])]

#eval do
  let base : Wasm.Store := {structs := [Workloads.object 1, Workloads.object 2]}
  let fast := Store.ofSpec base
  check "heap boundary roundtrip" (fast.toSpec == base)
  check "missing heap address" (fast.struct? ⟨2⟩ == none)
  let (address, grown) := fast.allocateStruct (Workloads.object 3)
  check "allocation address" (address.index == 2)
  check "allocation correspondence"
    (grown.toSpec == (base.allocateStruct (Workloads.object 3)).2)
  check "preserves earlier address" (grown.struct? ⟨0⟩ == fast.struct? ⟨0⟩)
  check "new object lookup" (grown.struct? address == some (Workloads.object 3))
  check "update correspondence"
    ((grown.writeStruct ⟨1⟩ (Workloads.object 4)).toSpec ==
      grown.toSpec.writeStruct ⟨1⟩ (Workloads.object 4))
  check "out of bounds update correspondence"
    ((grown.writeStruct ⟨99⟩ (Workloads.object 4)).toSpec ==
      grown.toSpec.writeStruct ⟨99⟩ (Workloads.object 4))
  for kind in ["allocate", "allocate-read", "linked", "read-early", "read-middle",
      "read-late", "control"] do
    for n in [1, 7, 35] do
      let c := Workloads.configuration kind n
      agreement s!"{kind}/{n}" c
      let result := runConfiguration (Workloads.fuel kind n) (Configuration.ofSpec c)
      check s!"{kind}/{n}: expected result"
        (result.status == RunStatus.finished (Workloads.expected kind n))
  for (name, source, expected) in fixtures do
    let c ← match prepare source with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"{name}: {e}")
    agreement name c
    let result := runConfiguration 10000 (Configuration.ofSpec c)
    check (name ++ ": expected result")
      (result.status ==
          if name == "null trap" then RunStatus.trapped else RunStatus.finished expected)
  for code in ([[], [.instr .drop], [.instr (.structNew 0 false)],
      [.instr (.const (.ref (.struct_ ⟨999⟩))), .instr (.refTest false .struct_)],
      [.instr (.call 0)], [.instr (.br 0)], [.instr .return_]] : List (List AdminInstr)) do
    agreement "invalid/terminal configuration" ⟨{}, {}, code⟩

#print axioms Wasm.Fast.Store.allocateStruct_toSpec
#print axioms Wasm.Fast.stepConfiguration_spec
#print axioms Wasm.Fast.runConfiguration_spec

end Wasm.Fast.Tests
