import Wasm.Text.Script

namespace Wasm.Text.Tests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def script (s : String) : IO Report := do
  match parse s with
  | .ok commands => return runScript commands
  | .error e => throw (IO.userError e)

#eval do
  check ((parse "(; outer (; nested ;) ;) ;; line\n(module)").isOk) "comments"
  for text in ["(", ")", "(;", "\"unterminated", "\"\\q\"", "\"\\u{d800}\""] do
    check (!(parse text).isOk) s!"must reject {text}"
  match parse "\"a\\00\\ff\\n\\u{1f600}\"" with
  | .ok [.string bytes] =>
    check (bytes == ByteArray.mk #[97, 0, 255, 10, 240, 159, 152, 128]) "string bytes"
  | _ => throw (IO.userError "string escapes")
  check (match integer 32 "-2147483648" with
    | .ok n => n == -2147483648 | _ => false) "signed minimum"
  check (match integer 32 "0xffff_ffff" with
    | .ok n => n == 4294967295 | _ => false) "unsigned maximum"
  for text in ["4294967296", "-2147483649", "0x", "1__2", "_1", "1_"] do
    check (!(integer 32 text).isOk) s!"bad literal {text}"
  let r ← script "
    (module $M
      (func $id (param $x i32) (result i32) local.get $x)
      (func (export \"twice\") (param i32) (result i32)
        (i32.add (call $id (local.get 0)) (local.get 0)))
      (func (export \"trap\") unreachable))
    (assert_return (invoke $M \"twice\" (i32.const -1)) (i32.const -2))
    (assert_trap (invoke \"trap\") \"unreachable\")
    (assert_return (invoke \"twice\" (i32.const 1)) (i32.const 3))
    (assert_return (invoke \"trap\"))
    (assert_trap (invoke \"twice\" (i32.const 1)) \"unreachable\")
    (assert_invalid (module) \"bad type\")
    (module (memory 1 shared))
    (assert_return (invoke \"twice\" (i32.const 1)) (i32.const 2))
    (assert_return (invoke $M \"twice\" (i32.const 1)) (i32.const 2))"
  check (r.passed == 4 && r.failed == 4 && r.unsupported == 2) "script outcomes"
  let validation ← script "
    (module $good (func (export \"f\") (result i32) (i32.const 7)))
    (assert_invalid (module (func (result i32) i32.add)) \"type mismatch\")
    (assert_invalid (module (func (result i32) i32.const 7)) \"type mismatch\")
    (assert_invalid (module (func (result f32) f32.const 0)) \"type mismatch\")
    (assert_invalid (module (func i32.const 4294967296)) \"type mismatch\")
    (assert_return (invoke \"f\") (i32.const 7))
    (module (func (export \"bad\") (result i32) i32.add))
    (assert_return (invoke \"f\") (i32.const 7))
    (assert_return (invoke $good \"f\") (i32.const 7))"
  check (validation.passed == 4 && validation.failed == 4 && validation.unsupported == 1)
    "validation assertions, phases, and state isolation"
  for text in [
    "(module (func block nop))",
    "(module (func else))",
    "(module (func block $a nop end $b))",
    "(module (func (block $a br $missing)))",
    "(module (func if else else end))",
    "(module (func (if (else nop))))"
  ] do
    let .ok [.list fields] := parse text | throw (IO.userError "parser fixture")
    check (match module (.list fields) with
      | .error (.invalid _) => true | _ => false) s!"control elaboration error: {text}"
  let .ok [expr] := parse "(module (func (result i32 i64)
    (block (result i32 i64) (i32.const 1) (i64.const 2))))" |
    throw (IO.userError "multi-result fixture")
  let .ok source := module expr | throw (IO.userError "multi-result elaboration")
  check (source.types.length == 1 && (Validation.validate source).isOk)
    "implicit indexed block signature"
  let fuel ← script "(module (func (export \"f\") nop)) (invoke \"f\")"
  check (fuel.failed == 0) "normal execution"
  let .ok commands := parse "(module (func (export \"f\") nop)) (invoke \"f\")" |
    throw (IO.userError "fuel fixture")
  check ((runScript commands 0).failed > 0) "fuel exhaustion cannot pass"

#eval (show IO Unit from do
  for text in [
    "(module (type $t (func)) (type $t (func)))",
    "(module (func (type $missing)))",
    "(module (type (func)) (func (type 0 0)))",
    "(module (type (func)) (func (type 0) (type 0)))",
    "(module (type (func (param i32))) (func (type 0) (param i64)))",
    "(module (type (func (param i32))) (func (type 0) (param)))",
    "(module (type (func (param i32) (result i32))) (func (type 0) (result i32)))",
    "(module (type (func (param $doc i32))) (func (type 0) local.get $doc drop))",
    "(module (type (func (param i32))) (func (type 0) (param $x i32) (local $x i64)))",
    "(module (type (func)) (func (block (type $missing))))",
    "(module (type (func (result i32))) (func (block (type 0) (result i64))))",
    "(module (func (block (param $x i32) drop)))",
    "(module (type (func (result i32) (param i32))))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "type fixture parse")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) s!"type elaboration error: {text}"
  let .ok [expr] := parse "(module
    (func (param i32) (result i32) local.get 0)
    (type $first (func (param i32) (result i32)))
    (type $second (func (param i32) (result i32)))
    (func (type $second) local.get 0)
    (func (param i32) (result i32) local.get 0))" |
    throw (IO.userError "type reuse parse")
  let .ok source := module expr | throw (IO.userError "type reuse elaboration")
  check (source.types.length == 2 && source.funcs.map Func.typeIdx == [0, 1, 0])
    "explicit duplicates retain indices; inferred types reuse the first definition"
  check ((Validation.validate source).isOk) "type reuse validation"
  let errors ← script "
    (module (func (export \"f\") (result i32) i32.const 7))
    (assert_invalid (module (type (func (result i32)))
      (func (type 0) (result i64) i64.const 0)) \"type mismatch\")
    (assert_return (invoke \"f\") (i32.const 7))"
  check (errors.passed == 2 && errors.failed == 1 && errors.unsupported == 0)
    "type elaboration errors cannot count as validator rejection"
  for text in ["(module (type (struct)))", "(module (type (func (param v128))))",
    "(module (rec (type (func))))"] do
    let .ok [expr] := parse text | throw (IO.userError "unsupported type fixture")
    check (match module expr with
      | .error (.unsupported _) => true | _ => false) "unsupported type forms")

#eval (show IO Unit from do
  for text in [
    "(module (table $t 0 funcref) (table $t 0 funcref))",
    "(module (elem $e func) (elem $e declare func))",
    "(module (func (call_indirect $missing)))",
    "(module (func (call_indirect (param $x i32))))",
    "(module (elem (table $missing) (i32.const 0) func))",
    "(module (elem (table 0) func))",
    "(module (elem declare (i32.const 0) func))",
    "(module (table funcref (elem $missing)))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "table fixture parse")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) s!"table elaboration error: {text}"
  let .ok [expr] := parse "(module
    (table $t (export \"t\") (export \"alias\") (ref null func) (elem $f))
    (func $f)
    (func (export \"call\") i32.const 0 call_indirect $t))" |
    throw (IO.userError "inline table parse")
  let .ok source := module expr | throw (IO.userError "inline table elaboration")
  check (source.tables.length == 1 && source.elems.length == 1 &&
    source.exports.length == 3 && (Validation.validate source).isOk)
    "inline table abbreviation, forward function names, and repeated table exports"
  let reports ← script "
    (module (table 0 funcref) (elem (i32.const 0) func))
    (module (func) (table 0 funcref) (elem (i32.const 0) func 0))"
  check (reports.passed == 1 && reports.failed == 1 && reports.unsupported == 0)
    "element bounds are instantiation traps, not validation rejection"
  for text in ["(module (table 1 (ref func)))",
    "(module (table 1 funcref) (func i32.const 0 v128.const))"] do
    let .ok [expr] := parse text | throw (IO.userError "unsupported table fixture")
    check (match module expr with
      | .error (.unsupported _) => true | _ => false) "unsupported reference/table forms")

#eval (show IO Unit from do
  let matching ← script "
    (module $M
      (func $f (export \"f\") (result funcref) ref.func $f)
      (func (export \"null\") (result funcref) ref.null func)
      (func (export \"extern\") (param externref) (result externref) local.get 0))
    (assert_return (invoke \"f\") (ref.func))
    (assert_return (invoke \"null\") (ref.null))
    (assert_return (invoke \"extern\" (ref.extern 7)) (ref.extern))
    (assert_return (invoke \"extern\" (ref.extern 7)) (ref.extern 7))
    (assert_return (invoke \"f\") (ref.null))
    (assert_return (invoke \"null\") (ref.func))
    (assert_return (invoke \"null\") (ref.extern))
    (assert_return (invoke \"extern\" (ref.extern 7)) (ref.extern 8))
    (assert_return (invoke \"f\"))
    (assert_return (invoke \"extern\" (ref.null extern)) (ref.null func))
    (module (func (export \"f\") (result funcref) ref.null func))
    (assert_return (invoke $M \"f\") (ref.func))"
  check (matching.passed == 7 && matching.failed == 6 && matching.unsupported == 0)
    "reference result patterns, exact external identity, arity, and named earlier instances"
  for text in ["(module (table 1 funcref) (func table.get $missing drop))",
    "(module (func ref.func $missing drop))", "(module (start 0) (start 0) (func))"] do
    let .ok [expr] := parse text | throw (IO.userError "reference fixture parse")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) "reference/start elaboration errors")

#eval show IO Unit from do
  for text in [
    "(module (table 1 funcref) (func table.copy 0))",
    "(module (table 1 funcref) (func (table.copy 0 (i32.const 0))))",
    "(module (table 1 funcref) (func table.copy $missing 0))",
    "(module (table 1 funcref) (func table.init))",
    "(module (table 1 funcref) (func table.init $missing))",
    "(module (elem func) (func elem.drop))",
    "(module (elem func) (func elem.drop $missing))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "bulk table syntax fixture")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) "malformed or unknown bulk table immediate"
  let .ok [expr] := parse "
    (module
      (func elem.drop $later (block table.init $later))
      (table funcref (elem))
      (elem $later func)
      (table funcref (elem))
      (elem $last func)
      (func (elem.drop $last)))" | throw (IO.userError "element index fixture")
  let .ok source := module expr | throw (IO.userError "element index elaboration")
  check (source.elems.length == 4 && match source.funcs with
    | [f, g] =>
      f.body == [.elemDrop 1, .block (.val none) [.tableInit 0 1]] && g.body == [.elemDrop 3]
    | _ => false)
    "forward element names count implicit segments and reach nested instructions"

#eval show IO Unit from do
  for text in [
    "(module (func) (import \"m\" \"t\" (table 0 funcref)))",
    "(module (table 0 funcref) (func (import \"m\" \"f\")))",
    "(module (func (import \"m\" \"f\") nop))",
    "(module (func (import \"m\" \"f\") (local i32)))",
    "(module (import \"m\" \"f\" (func $f)) (func $f))",
    "(module (import \"m\" \"t\" (table $t 0 funcref)) (table $t 0 funcref))",
    "(module (table (import \"m\" \"t\") funcref (elem)))",
    "(module (func (import \"m\")))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "import syntax fixture")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) "malformed import declaration"
  let failures ← script "
    (module $ok (func (export \"f\")))
    (register \"m\" $ok)
    (assert_unlinkable (module (import \"m\" \"f\" (func))) \"linkable\")
    (assert_unlinkable (module (func drop)) \"invalid, not unlinkable\")
    (register \"m\" $missing)
    (module $after (import \"m\" \"f\" (func $f)) (func (export \"f\") call $f))
    (invoke \"f\")
    (module $blocked (memory 0 shared))
    (register \"m\" $blocked)
    (module (import \"m\" \"f\" (func)))
    (assert_unlinkable (module (import \"m\" \"f\" (func))) \"blocked\")"
  check (failures.passed == 4 && failures.failed == 3 && failures.unsupported == 4)
    "linkable/invalid assertions fail; unknown registration fails; blocked binding replaces old one"

#eval show IO Unit from do
  let host ← script "
    (module (import \"spectest\" \"print\" (func)))
    (assert_unlinkable (module (import \"spectest\" \"print\" (func))) \"host unavailable\")
    (module (func (export \"print\")))
    (register \"spectest\")
    (module (import \"spectest\" \"print\" (func $p)) (start $p))"
  check (host.passed == 4 && host.failed == 1 && host.unsupported == 0)
    "spectest is predefined and linkable; explicit registration can replace it"

#eval show IO Unit from do
  for text in [
    "(module (global $g i32 (i32.const 0)) (global $g i32 (i32.const 1)))",
    "(module (import \"m\" \"g\" (global $g i32)) (global $g i32 (i32.const 0)))",
    "(module (global (import \"m\" \"g\") i32 (i32.const 0)))",
    "(module (global (mut i32 i64) (i32.const 0)))",
    "(module (global i32 (global.get $missing)))",
    "(module (func global.set $missing))",
    "(module (export \"g\" (global $missing)))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "global syntax fixture")
    check (match module expr with
      | .error (.invalid _) => true | _ => false) "bad global syntax or identifier"
  let actions ← script "
    (module $m (global (export \"g\") i32 (i32.const 1)) (func (export \"f\")))
    (assert_return (get \"g\") (i32.const 2))
    (assert_return (get \"g\"))
    (assert_trap (get \"g\") \"no trap\")
    (get \"f\")
    (get \"missing\")
    (get $missing \"g\")
    (get \"g\" (i32.const 0))
    (module)
    (assert_return (get $m \"g\") (i32.const 1))"
  check (actions.passed == 3 && actions.failed == 7 && actions.unsupported == 0)
    "get action checks export kind, module ID, argument/result arity, and expected value"
  for text in [
    "(module (global funcref (ref.null func)) (table 1 funcref (global.get 0)))",
    "(module (table 1 funcref (ref.null func)))"
  ] do
    let .ok [expr] := parse text | throw (IO.userError "table initializer fixture")
    check (match module expr with
      | .ok _ => true | _ => false) "explicit table initializers elaborate"

#eval show IO Unit from do
  for text in [
    "(module (memory $m 0) (memory $m 0))",
    "(module (data $d) (data $d))",
    "(module (memory (import \"m\" \"x\") (data \"x\")))",
    "(module (memory 0) (import \"m\" \"x\" (memory 0)))",
    "(module (memory 1) (func i32.const 0 i32.load align=3 drop))",
    "(module (memory 1) (func i32.const 0 i32.load align=0 drop))",
    "(module (memory 1) (func i32.const 0 i32.load offset=18446744073709551616 drop))",
    "(module (memory 1) (func memory.copy 0))",
    "(module (memory 1) (data (memory 0) \"x\"))"] do
    let .ok [expr] := parse text | throw (IO.userError "memory parser fixture")
    check (match Wasm.Text.module expr with
      | .error (.invalid _) => true | _ => false) "invalid memory text syntax"

end Wasm.Text.Tests
