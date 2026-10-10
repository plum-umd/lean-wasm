import Wasm.Stepper
import Wasm.Validation

namespace Wasm.Tests

open AdminInstr Instr

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"integer regression failed: {name}")

private def same {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => same

private def integerTests : IO Unit := do
  let widths : List (ValType × Nat × (Int → Value)) :=
    [(.i32, 32, fun i => .i32 (BitVec.ofInt 32 i)),
     (.i64, 64, fun i => .i64 (BitVec.ofInt 64 i))]
  for (t, n, pack) in widths do
    let high : Int := 2 ^ (n - 1)
    let all : Int := 2 ^ n - 1
    let binaryCases : List (IntBinaryOp × Int × Int × Int) :=
      [(.divS, -7, 3, -2), (.divS, 7, -3, -2), (.divS, -7, -3, 2),
       (.remS, -7, 3, -1), (.remS, 7, -3, 1), (.remS, -7, -3, -1),
       (.remS, -high, -1, 0), (.divS, -high, 1, -high),
       (.divU, all, 2, high - 1), (.remU, all, 2, 1),
       (.and_, 12, 10, 8), (.or_, 12, 10, 14), (.xor, 12, 10, 6),
       (.shl, 6, 1, 12), (.shrU, all, 1, high - 1), (.shrS, -7, 1, -4),
       (.rotl, high, 1, 1), (.rotr, 1, 1, high),
       (.shl, 7, n, 7), (.shrU, 7, n, 7), (.shrS, -7, n, -7),
       (.rotl, 7, n, 7), (.rotr, 7, n, 7),
       (.shl, 7, 2 * n + 1, 14), (.shrU, 14, 2 * n + 1, 7),
       (.shrS, -7, 2 * n + 1, -4),
       (.rotl, high, 2 * n + 1, 1), (.rotr, 1, 2 * n + 1, high),
       (.shl, 1, all, high), (.shrU, high, all, 1), (.shrS, -high, all, -1)]
    for (op, a, b, expected) in binaryCases do
      check s!"{reprStr t} {reprStr op} {a} {b}" (step []
        [instr (.const (pack a)), instr (.const (pack b)), instr (.intBinary t op)] ≟
        some (values [pack expected]))
    for op in [IntBinaryOp.divS, .divU, .remS, .remU] do
      check s!"{reprStr t} {reprStr op} division by zero" (step []
        [instr (.const (pack 7)), instr (.const (pack 0)), instr (.intBinary t op)] ≟
        some [.trap])
    check s!"{reprStr t} signed division overflow" (step []
      [instr (.const (pack (-high))), instr (.const (pack (-1))), instr (.intBinary t .divS)] ≟
      some [.trap])
    let unaryCases : List (IntUnaryOp × Int × Nat) :=
      [(.clz, 0, n), (.ctz, 0, n), (.popcnt, 0, 0),
       (.clz, 1, n - 1), (.ctz, 1, 0), (.popcnt, 1, 1),
       (.clz, all, 0), (.ctz, all, 0), (.popcnt, all, n),
       (.clz, high, 0), (.ctz, high, n - 1), (.popcnt, high, 1)]
    for (op, a, expected) in unaryCases do
      check s!"{reprStr t} {reprStr op} {a}" (step [] [instr (.const (pack a)), instr (.intUnary t op)] ≟
        some (values [pack expected]))
    let relCases : List (IntRelOp × Bool × Bool) :=
      [(.eq, false, true), (.ne, true, false), (.ltS, true, false), (.ltU, false, false),
       (.gtS, false, false), (.gtU, true, false), (.leS, true, true), (.leU, false, true),
       (.geS, false, true), (.geU, true, true)]
    for (op, unequal, equal) in relCases do
      for (b, expected) in [(1, unequal), (-1, equal)] do
        check s!"{reprStr t} {reprStr op} -1 {b}" (step [] [instr (.const (pack (-1))),
          instr (.const (pack b)), instr (.intRel t op)] ≟
          some (values [.i32 (if expected then 1 else 0)]))
    -- Context preservation, nested execution, and numeric trap propagation.
    check s!"{reprStr t} numeric trap in nested label" ((run 10 []
      [instr (.const (pack 42)), .label 0 [] [instr (.const (pack 7)),
        instr (.const (pack 0)), instr (.intBinary t .divU)]]).status ≟ .trapped)
    check s!"{reprStr t} bit operation in nested label" ((run 10 []
      [instr (.const (pack 42)), .label 1 [] [instr (.const (pack 12)),
        instr (.const (pack 10)), instr (.intBinary t .and_)]]).status ≟
        .finished [pack 42, pack 8])
  let conversions : List (IntConversion × Value × Value) :=
    [(.wrapI64, .i64 4294967297, .i32 1),
     (.extendI32S, .i32 4294967295, .i64 18446744073709551615),
     (.extendI32U, .i32 4294967295, .i64 4294967295),
     (.extendI32_8S, .i32 384, .i32 4294967168),
     (.extendI32_16S, .i32 98304, .i32 4294934528),
     (.extendI64_8S, .i64 384, .i64 18446744073709551488),
     (.extendI64_16S, .i64 98304, .i64 18446744073709518848),
     (.extendI64_32S, .i64 6442450944, .i64 18446744071562067968),
     (.extendI32_8S, .i32 383, .i32 127),
     (.extendI32_16S, .i32 98303, .i32 32767),
     (.extendI64_8S, .i64 383, .i64 127),
     (.extendI64_16S, .i64 98303, .i64 32767),
     (.extendI64_32S, .i64 6442450943, .i64 2147483647)]
  for (op, a, expected) in conversions do
    check s!"{reprStr op} conversion" (step [] [instr (.const a), instr (.intConvert op)] ≟
      some (values [expected]))
  check "conversion type mismatch" (stepOutcome []
    [instr (.const (.i64 1)), instr (.intConvert .extendI32S)] ≟ .stuck)
  check "binary type mismatch is stuck, not a trap" (stepOutcome []
    [instr (.const (.i32 7)), instr (.const (.i64 0)), instr (.intBinary .i32 .divS)] ≟ .stuck)
  check "binary underflow" (stepOutcome []
    [instr (.const (.i32 7)), instr (.intBinary .i32 .divU)] ≟ .stuck)
  check "unary underflow" (stepOutcome [] [instr (.intUnary .i32 .clz)] ≟ .stuck)
  check "comparison type mismatch" (stepOutcome []
    [instr (.const (.i32 7)), instr (.const (.i64 1)), instr (.intRel .i32 .eq)] ≟ .stuck)

#eval integerTests

example : evalIntBinary .divS (BitVec.ofInt 32 (-7)) 3 =
    some (BitVec.ofInt 32 (-2)) := by decide
example : evalIntBinary .remS (BitVec.ofInt 32 (-7)) 3 =
    some (BitVec.ofInt 32 (-1)) := by decide
example : evalIntBinary .remS (BitVec.ofInt 32 (-2147483648))
    (BitVec.ofInt 32 (-1)) = some 0 := by decide
example : InstrTyping (.intRel .i64 .ltS) [.i64, .i64] [.i32] := .intRel
example : InstrTyping (.intConvert .wrapI64) [.i64] [.i32] := .intConvert
example : InstrTyping (.intConvert .extendI32S) [.i32] [.i64] := .intConvert
example : InstrTyping (.intUnary .i64 .popcnt) [.i64] [.i64] := .intUnary
example : InstrTyping (.intBinary .i32 .divS) [.i32, .i32] [.i32] := .intBinary

#print axioms Wasm.reduceInteger_sound
#print axioms Wasm.reduceInteger_complete
#print axioms Wasm.divS_undefined_iff
#print axioms Wasm.remS_defined_iff
#print axioms Wasm.divS_spec
#print axioms Wasm.remS_spec
#print axioms Wasm.evalUnary_type
#print axioms Wasm.evalRel_type
#print axioms Wasm.evalConversion_type

end Wasm.Tests
