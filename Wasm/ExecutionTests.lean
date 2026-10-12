import Wasm.DepthWorkloads
import Wasm.MachineExecution
import Wasm.Workloads
import Wasm.Text.Module
import Wasm.Instantiation
import Wasm.ExecutableValidationSoundness

namespace Wasm.Execution.Tests

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"fast executor regression: {name}")

-- Compare API boundaries and fuel composition, retaining one execution implementation.
private def execution (name : String) (c : Wasm.Configuration) : IO Unit := do
  let fast := Configuration.ofSpec c
  let initial := Machine.ofConfiguration fast
  check (name ++ ": input roundtrip") (fast.toSpec == c)
  check (name ++ ": normalize") ((Machine.normalize initial).toSpec == c)
  for budget in [0, 1, 2, 3, 5, 10, 40, 200, 10000] do
    let result := Machine.run budget initial
    let publicResult := Wasm.runConfiguration budget c
    check (name ++ s!": public boundary/fuel {budget}")
      (publicResult.state == result.state.toSpec && publicResult.status == result.status)
    check (name ++ s!": optional-step boundary {budget}")
      (Wasm.stepConfiguration publicResult.state == (Machine.step result.state).map Machine.toSpec)
    let resumed := Machine.run 10000 result.state
    let combined := Machine.run (budget + 10000) initial
    check (name ++ s!": fuel composition {budget}")
      (resumed.state.toSpec == combined.state.toSpec && resumed.status == combined.status)
    let boundaryResumed := Wasm.runConfiguration 10000 publicResult.state
    check (name ++ s!": resume boundary {budget}")
      (boundaryResumed.state == resumed.state.toSpec && boundaryResumed.status == resumed.status)

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
  ("multi-value branch", "(module
    (func (export \"main\") (result i32 i64)
      i32.const 11 i64.const 22
      block $out (param i32 i64) (result i32 i64)
        block (result i32 i64)
          i32.const 7 i64.const 9 br $out
        end unreachable
      end))", [.i32 7, .i64 9]),
  ("tail call through handler", "(module
    (func $g (result i32) i32.const 42)
    (func $f (result i32)
      try_table
        block return_call $g end
      end i32.const 0)
    (func (export \"main\") (result i32) call $f))", [.i32 42]),
  ("rethrow caught reference", "(module (tag $e (param i32))
    (func (export \"main\") (result i32)
      block $out (result i32)
        try_table (catch $e $out)
          block $ref (result exnref)
            try_table (catch_all_ref $ref) i32.const 42 throw $e end
            unreachable
          end throw_ref
        end unreachable
      end))", [.i32 42]),
  ("global mutation", "(module (global $g (mut i32) (i32.const 0))
    (func (export \"main\") (result i32)
      i32.const 42 global.set $g global.get $g))", [.i32 42]),
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
      execution s!"{kind}/{n}" c
      let result := runConfiguration (Workloads.fuel kind n) (Configuration.ofSpec c)
      check s!"{kind}/{n}: expected result"
        (result.status == RunStatus.finished (Workloads.expected kind n))
  for kind in DepthWorkloads.kinds do
    for depth in [0, 1, 3, 10, 32] do
      let c := DepthWorkloads.configuration kind 3 depth
      execution s!"depth/{kind}/{depth}" c
      let result := Machine.run (DepthWorkloads.fuel 3 depth)
        (Machine.ofConfiguration (Configuration.ofSpec c))
      check s!"depth/{kind}/{depth}: expected result"
        (result.status == DepthWorkloads.expected kind 3)
  for (name, source, expected) in fixtures do
    let c ← match prepare source with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"{name}: {e}")
    execution name c
    let result := runConfiguration 10000 (Configuration.ofSpec c)
    check (name ++ ": expected result")
      (result.status ==
          if name == "null trap" then RunStatus.trapped else RunStatus.finished expected)
  for operandDepth in [0, 1, 32, 128] do
    let code := values ((List.range operandDepth).map fun n => .i64 (BitVec.ofNat 64 n)) ++
      instructions [.const (.i64 7), .const (.i64 9), .binop .i64 .add]
    execution s!"operand-prefix/{operandDepth}" ⟨{}, {}, code⟩
  for code in ([[], [.instr .drop], [.instr (.structNew 0 false)],
      [.instr (.const (.ref (.struct_ ⟨999⟩))), .instr (.refTest false .struct_)],
      [.instr (.call 0)], [.instr (.br 0)], [.instr .return_],
      [.instr (.const (.ref (.null .nofunc))), .invokeDefined ⟨[], 0⟩],
      [.instr (.const (.ref (.null .nofunc))), .returnInvokeDefined ⟨[], 0⟩],
      [.frame 0 {} (values [.i32 1])],
      [.frame 1 {} (values [.i32 1] ++ instructions [.return_])],
      [.handler [] [.trap]], [.frame 0 {} [.throwing ⟨999⟩]]] : List (List AdminInstr)) do
    execution "invalid/terminal configuration" ⟨{}, {}, code⟩

-- Exercise opcode routing and arity selection with both usable and malformed operands.
#eval show IO Unit from do
  let source := "(module
    (type $s (struct (field (mut i32))))
    (type $a (array (mut i32)))
    (type $f (func (param i32) (result i32)))
    (func $id (type $f) local.get 0)
    (table 2 funcref) (elem (i32.const 0) $id)
    (memory 0 0) (data \"abcd\")
    (global $g (mut i32) (i32.const 0)) (tag $e (param i32))
    (func (export \"main\") (result i32) i32.const 0))"
  let base ← match prepare source with
    | .ok c => pure c
    | .error error => throw (IO.userError error)
  let setup := instructions [.const (.i32 1), .structNew 0 false, .drop,
    .const (.i32 2), .arrayOp (.new_ 1 true), .drop]
  let initialized := Wasm.runConfiguration 10000 {base with code := setup}
  let frame := {base.frame with locals := [some (.i32 0), some (.i64 0)]}
  let stacks : List (List Value) := [[], [.i32 0], [.i32 1], [.i64 0],
    [.ref (.null .any)], [.ref (.null .nofunc)], [.ref (.struct_ ⟨0⟩)],
    [.ref (.func ⟨0⟩)], [.i32 0, .i32 42], [.i32 0, .i32 42, .i32 2],
    [.ref (.struct_ ⟨0⟩), .i32 42], [.i32 7, .ref (.func ⟨0⟩)], [.v128 0, .v128 1]]
  let ops : List Instr := [Instr.nop, Instr.unreachable, Instr.drop, Instr.select none,
    Instr.binop .i32 .add, Instr.eqz .i32, Instr.intBinary .i32 .divU, Instr.intUnary .i32 .clz,
    Instr.intRel .i32 .eq, Instr.intConvert .extendI32U,
    Instr.localGet 0, Instr.localSet 0, Instr.localTee 0, Instr.localSet 999,
    Instr.globalGet 0, Instr.globalSet 0, Instr.load .i32 0 ⟨0, 0⟩, Instr.store .i32 0 ⟨0, 0⟩,
    Instr.memorySize 0, Instr.memoryGrow 0, Instr.memoryFill 0, Instr.memoryCopy 0 0,
    Instr.memoryInit 0 0,
    Instr.dataDrop 0, Instr.call 0, Instr.callRef 2, Instr.callIndirect 0 2, Instr.returnCall 0,
    Instr.returnCallRef 2, Instr.returnCallIndirect 0 2, Instr.refNull .any, Instr.refFunc 0,
    Instr.refIsNull,
    Instr.gcReference .eq, Instr.gcReference .i31New, Instr.refAsNonNull,
    Instr.refTest true (.typeIdx 0), Instr.refCast false (.typeIdx 0),
    Instr.brOnNull 0, Instr.brOnNonNull 0, Instr.structNew 0 false, Instr.structNew 0 true,
    Instr.structGet 0 0 none, Instr.structSet 0 0, Instr.arrayOp (.new_ 1 true),
    Instr.arrayOp (.new_ 1 false), Instr.arrayOp (.newFixed 1 2), Instr.arrayOp .len,
    Instr.arrayOp (.get 1 none), Instr.arrayOp (.set 1), Instr.tableGet 0, Instr.tableSet 0,
    Instr.tableSize 0, Instr.tableGrow 0, Instr.tableFill 0, Instr.tableCopy 0 0,
    Instr.tableInit 0 0,
    Instr.elemDrop 0, Instr.throw_ 0, Instr.throwRef, Instr.return_, Instr.br 0, Instr.br 1,
    Instr.brIf 0,
    Instr.brTable [0, 1] 2, Instr.block (.val none) [Instr.nop], Instr.loop (.val none) [Instr.nop],
    Instr.if_ (.val none) [Instr.nop] [Instr.unreachable],
    Instr.tryTable (.val none) [] [Instr.nop],
    Instr.vector {opcode := .i32x4_add}]
  for op in ops do
    for stack in stacks do
      let body := values stack ++ [.instr op]
      for code in [body, [.label 1 [] body],
          [.frame 1 frame [.label 1 [] [.handler [.all 0 true] [.label 1 [] body]]]]] do
        let c : Wasm.Configuration := ⟨initialized.state.store, frame, code⟩
        let machine := Machine.ofConfiguration (Configuration.ofSpec c)
        let name := s!"dispatch-matrix/{repr op}/{stack.length}"
        check (name ++ ": optional step")
          (Wasm.stepConfiguration c == (Machine.step machine).map Machine.toSpec)
        let expected := Machine.run 5 (Machine.normalize machine)
        let actual := Machine.run 5 machine
        check (name ++ ": five-step run")
          (expected.state.toSpec == actual.state.toSpec && expected.status == actual.status)

#print axioms Wasm.Execution.Store.allocateStruct_toSpec
#print axioms Wasm.Execution.stepConfiguration_spec
#print axioms Wasm.Execution.Machine.step_spec
#print axioms Wasm.Execution.Machine.normalize_same
#print axioms Wasm.Execution.Machine.run_status_spec
#print axioms Wasm.Execution.Machine.run_spec
#print axioms Wasm.Execution.runConfiguration_spec

end Wasm.Execution.Tests
