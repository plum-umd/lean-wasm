import Wasm.Stepper

namespace Wasm.Tests

open AdminInstr Instr

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"stepper regression failed: {name}")

private def same {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected

local infix:50 " ≟ " => same

-- These checks execute compiled Lean code, while soundness is proved in Stepper.lean.
#eval do
  let i32 (n : Nat) := instr (.const (.i32 (BitVec.ofNat 32 n)))
  let i64 (n : Nat) := instr (.const (.i64 (BitVec.ofNat 64 n)))
  let empty : BlockType := .val none
  check "empty program" (stepOutcome [] [] ≟ .finished [])
  check "value order" (stepOutcome [] [i32 3, i64 7] ≟ .finished [.i32 3, .i64 7])
  check "nop context" (step [] [i32 42, instr .nop, instr .drop] ≟
    some [i32 42, instr .drop])
  check "unreachable context" (step [] [i32 42, instr .unreachable, instr .drop] ≟
    some [i32 42, .trap, instr .drop])
  check "trap collapse" (step [] [i32 42, .trap, instr .drop] ≟ some [.trap])
  check "terminal trap" (stepOutcome [] [.trap] ≟ .trapped)
  check "drop" (step [] [i32 42, i64 7, instr .drop] ≟ some [i32 42])
  check "subtraction order and suffix" (step [] [i32 42, i32 9, i32 4,
    instr (.binop .i32 .sub), instr .drop] ≟ some [i32 42, i32 5, instr .drop])
  check "i64 addition overflow" (step [] [i64 18446744073709551615, i64 1,
    instr (.binop .i64 .add)] ≟ some [i64 0])
  check "multiplication" (step [] [i32 6, i32 7, instr (.binop .i32 .mul)] ≟ some [i32 42])
  check "i64 eqz" (step [] [i64 0, instr (.eqz .i64)] ≟ some [i32 1])
  check "select zero" (step [] [i64 7, i64 8, i32 0, instr (.select none)] ≟ some [i64 8])
  check "select nonzero" (step [] [i64 7, i64 8, i32 2,
    instr (.select (some [.i64]))] ≟ some [i64 7])
  check "if zero" (step [] [i32 42, i32 0, instr (.if_ empty [.unreachable] [.nop])] ≟
    some [i32 42, instr (.block empty [.nop])])
  check "if nonzero" (step [] [i32 7, instr (.if_ empty [.nop] [.unreachable])] ≟
    some [instr (.block empty [.nop])])
  check "br_if zero preserves operands" (step [] [i32 42, i32 0, instr (.brIf 0)] ≟
    some [i32 42])
  check "br_if taken" (step [] [i32 42, i32 7, instr (.brIf 0)] ≟
    some [i32 42, instr (.br 0)])
  check "br_table hit" (step [] [i32 1, instr (.brTable [4, 6] 8)] ≟ some [instr (.br 6)])
  check "br_table boundary" (step [] [i32 2, instr (.brTable [4, 6] 8)] ≟
    some [instr (.br 8)])
  check "br_table unsigned index" (step [] [i32 4294967295, instr (.brTable [4, 6] 8)] ≟
    some [instr (.br 8)])
  check "br_table empty" (step [] [i32 0, instr (.brTable [] 8)] ≟ some [instr (.br 8)])
  check "block entry" (step [] [i32 42, instr (.block empty [.nop]), instr .drop] ≟
    some [i32 42, .label 0 [] [instr .nop], instr .drop])
  let types : TypeContext := [.func ⟨[.i32, .i64], [.i32]⟩, .func ⟨[.i32], [.i32, .i64]⟩]
  check "multi-value block parameters" (step types [i32 42, i32 3, i64 7,
    instr (.block (.typeIdx 0) [.drop])] ≟
    some [i32 42, .label 1 [] [i32 3, i64 7, instr .drop]])
  check "loop parameter arity" (step types [i32 42, i32 3, instr (.loop (.typeIdx 1) [])] ≟
    some [i32 42, .label 1 [.loop (.typeIdx 1) []] [i32 3]])
  check "normal label completion" (step [] [.label 1 [.loop empty []] [i32 3, i64 7]] ≟
    some [i32 3, i64 7])
  check "branch values and discarded suffix" (step []
    [i32 42, .label 2 [] [i32 99, i64 7, i32 3, instr (.br 0), instr .unreachable],
      instr .drop] ≟ some [i32 42, i64 7, i32 3, instr .drop])
  check "zero-arity branch" (step []
    [.label 0 [] [i32 99, instr (.br 0), instr .unreachable]] ≟ some [])
  check "branch across label" (step []
    [.label 0 [.unreachable] [i32 99, i64 7, instr (.br 1), instr .unreachable]] ≟
    some [i32 99, i64 7, instr (.br 0)])
  check "loop branch continuation" (step types
    [.label 1 [.loop (.typeIdx 1) []] [i32 99, i32 3, instr (.br 0)]] ≟
    some [i32 3, instr (.loop (.typeIdx 1) [])])
  check "nested label stepping" (step [] [.label 0 [] [.label 0 [] [instr .nop]]] ≟
    some [.label 0 [] [.label 0 [] []]])
  check "nested trap" ((run 10 []
    [.label 0 [] [.label 0 [] [instr .unreachable]]]).status ≟ .trapped)
  check "drop underflow" (stepOutcome [] [instr .drop] ≟ .stuck)
  check "binop underflow" (stepOutcome [] [i32 1, instr (.binop .i32 .add)] ≟ .stuck)
  check "mixed numeric widths" (stepOutcome [] [i32 1, i64 2,
    instr (.binop .i32 .add)] ≟ .stuck)
  check "wrong condition width" (stepOutcome [] [i64 0, instr (.brIf 0)] ≟ .stuck)
  check "invalid block type index" (stepOutcome [] [instr (.block (.typeIdx 0) [])] ≟ .stuck)
  check "missing block parameters" (stepOutcome types [i32 3,
    instr (.block (.typeIdx 0) [])] ≟ .stuck)
  check "missing branch values" (stepOutcome [] [.label 1 [] [instr (.br 0)]] ≟ .stuck)
  check "unbound branch" (stepOutcome [] [instr (.br 0)] ≟ .stuck)
  check "labels isolate operand stacks" (stepOutcome []
    [i32 42, .label 0 [] [instr .drop]] ≟ .stuck)
  check "arithmetic run" ((run 10 [] [i32 9, i32 4,
    instr (.binop .i32 .sub)]).status ≟ .finished [.i32 5])
  check "selected conditional run" ((run 10 [] [i32 0, instr (.if_ (.val (some .i32))
    [.unreachable] [.const (.i32 9), .const (.i32 4), .binop .i32 .sub])]).status ≟
    .finished [.i32 5])
  check "nested branch run" ((run 10 [] [.label 1 [] [.label 0 []
    [i32 99, i64 7, instr (.br 1), instr .unreachable]]]).status ≟ .finished [.i64 7])
  check "multi-value block run" ((run 10 types [i32 42, i32 3, i64 7,
    instr (.block (.typeIdx 0) [.drop])]).status ≟ .finished [.i32 42, .i32 3])
  check "loop fallthrough" ((run 10 [.func ⟨[.i32], [.i32, .i64]⟩]
    [i32 3, instr (.loop (.typeIdx 0) [.const (.i64 7)])]).status ≟
    .finished [.i32 3, .i64 7])
  let infinite := [instr (.loop empty [.br 0])]
  check "loop exhaustion" ((run 20 [] infinite).status ≟ .exhausted)
  check "loop residual state" ((run 2 [] infinite).state ≟ infinite)
  check "zero-fuel residual" ((run 0 [] [instr .nop]).state ≟ [instr .nop])
  check "zero-fuel exhaustion" ((run 0 [] [instr .nop]).status ≟ .exhausted)
  check "zero-fuel finished" ((run 0 [] [i32 3]).status ≟ .finished [.i32 3])
  check "zero-fuel trap" ((run 0 [] [.trap]).status ≟ .trapped)
  check "zero-fuel stuck" ((run 0 [] [instr .drop]).status ≟ .stuck)
  check "last-fuel completion" ((run 1 [] [instr .nop]).status ≟ .finished [])
  check "block entry consumes one step" ((run 1 [] [instr (.block empty [])]).status ≟
    .exhausted)
  check "empty block consumes two steps" ((run 2 [] [instr (.block empty [])]).status ≟
    .finished [])
  let partialRun := run 1 [] [i32 0, instr (.if_ (.val (some .i32))
    [.unreachable] [.const (.i32 9), .const (.i32 4), .binop .i32 .sub])]
  check "resume after exhaustion" ((run 10 [] partialRun.state).status ≟ .finished [.i32 5])

#print axioms Wasm.step_sound
#print axioms Wasm.run_sound
#print axioms Wasm.run_finished
#print axioms Wasm.run_trapped

end Wasm.Tests
