import Wasm.Control
import Wasm.ControlValidation
import Wasm.ControlChoice

namespace Wasm.Tests

open AdminInstr Instr

private def emptyBlock : BlockType := .val none

-- Multi-value block entry moves just the parameters inside the label.
example : ControlReduces [.func ⟨[.i32, .i64], [.i32]⟩]
    (values [.i32 3, .i64 7] ++ [instr (.block (.typeIdx 0) [.drop])])
    [.label 1 [] (values [.i32 3, .i64 7] ++ instructions [.drop])] :=
  .block (ft := ⟨[.i32, .i64], [.i32]⟩) rfl rfl

-- Loop branch arity is its parameter count, even when result count differs.
example : ControlReduces [.func ⟨[.i32], [.i32, .i64]⟩]
    (values [.i32 3] ++ [instr (.loop (.typeIdx 0) [])])
    [.label 1 [.loop (.typeIdx 0) []] (values [.i32 3])] :=
  .loop (ft := ⟨[.i32], [.i32, .i64]⟩) rfl rfl

-- Normal completion does not execute a loop's backward continuation.
example : ControlReduces [] [.label 1 [.loop emptyBlock []] (values [.i32 3, .i64 7])]
    (values [.i32 3, .i64 7]) := .labelDone

-- A branch drops excess operands and the unexecuted suffix, keeping the top n values.
example : ControlReduces []
    [.label 2 [] (values [.i32 99] ++ values [.i64 7, .i32 3] ++
      [instr (.br 0)] ++ [instr .unreachable])]
    (values [.i64 7, .i32 3]) :=
  .brZero (discarded := [.i32 99]) (results := [.i64 7, .i32 3]) rfl

example : ControlReduces []
    [.label 1 [.loop (.typeIdx 0) []] (values [.i32 3] ++ [instr (.br 0)] ++ [])]
    (values [.i32 3] ++ instructions [.loop (.typeIdx 0) []]) :=
  .brZero (discarded := []) (results := [.i32 3]) rfl

-- Branch tables interpret even 0xffffffff as an unsigned index and use the default.
example : ControlReduces []
    [instr (.const (.i32 1)), instr (.brTable [4, 6] 8)] [instr (.br 6)] :=
  .brTableHit rfl
example : ControlReduces []
    [instr (.const (.i32 2)), instr (.brTable [4, 6] 8)] [instr (.br 8)] :=
  .brTableDefault (by decide)
example : ControlReduces []
    [instr (.const (.i32 4294967295)), instr (.brTable [4, 6] 8)] [instr (.br 8)] :=
  .brTableDefault (by decide)
example : ControlReduces []
    [instr (.const (.i32 0)), instr (.brTable [] 8)] [instr (.br 8)] :=
  .brTableDefault (by decide)

example : ControlReduces []
    [instr (.const (.i32 0)), instr (.brIf 2)] [] := .brIfZero
example : ControlReduces []
    [instr (.const (.i32 7)), instr (.brIf 2)] [instr (.br 2)] :=
  .brIfNonzero (by decide)

-- Crossing the inner label preserves all values until the outer target is reached.
example : ExecSteps []
    [.label 1 [] [.label 0 []
      (values [.i32 99, .i64 7] ++ [instr (.br 1)] ++ [instr .unreachable])]]
    (values [.i64 7]) :=
  .cons (.label (.control (.brSucc (vs := [.i32 99, .i64 7]))))
    (.cons (.control (.brZero (discarded := [.i32 99]) (results := [.i64 7]) rfl)) .refl)

-- Evaluate a selected branch through block entry, arithmetic, and label completion.
example : ExecSteps []
    [instr (.const (.i32 0)), instr (.if_ (.val (some .i32))
      [.unreachable] [.const (.i32 9), .const (.i32 4), .binop .i32 .sub])]
    (values [.i32 5]) :=
  .cons (.control .ifZero)
    (.cons (.control (.block (args := []) rfl rfl))
      (.cons (.label (.primitive (.binop (result := .i32 5) (by decide))))
        (.cons (.control (.labelDone (vs := [.i32 5]))) .refl)))

-- Untaken br_if preserves operands below its consumed condition.
example : ExecSteps []
    [.label 1 [] (values [.i32 3, .i32 0] ++ [instr (.brIf 0)])]
    (values [.i32 3]) :=
  .cons (.label (.context (vs := [.i32 3]) (tail := []) (.control .brIfZero)))
    (.cons (.control (.labelDone (vs := [.i32 3]))) .refl)

-- Traps propagate through each administrative label.
example : ExecSteps [] [.label 0 [] [.label 0 [] [instr .unreachable]]] [.trap] :=
  .cons (.label (.label (.primitive .unreachable)))
    (.cons (.label (.control .labelTrap)) (.cons (.control .labelTrap) .refl))

-- Block typing uses results for the branch target; loop typing uses parameters.
example : ControlInstrTyping [] [] (.block (.val (some .i32))
    [.const (.i32 7), .br 0]) [] [.i32] :=
  .block (ft := ⟨[], [.i32]⟩) rfl (.cons (.plain .const)
    (.cons (.br (input := []) rfl) .empty))

example : ControlInstrTyping [.func ⟨[.i32], [.i64]⟩] [] (.loop (.typeIdx 0) [.br 0])
    [.i32] [.i64] :=
  .loop (ft := ⟨[.i32], [.i64]⟩) rfl (.cons (.br (input := []) rfl) .empty)

example : ControlInstrTyping [] [[.i32], [.i32]] (.brTable [0, 1] 0)
    [.i32, .i32] [.i64] :=
  .brTable (input := []) (targets := [0, 1]) (ts := [.i32]) rfl
    (by intro l hl; simp at hl; rcases hl with rfl | rfl <;> rfl)

example : BlockType.resolve [] (.typeIdx 0) = none := rfl

example : reduceControlChoice [instr (.const (.i32 0)),
    instr (.if_ emptyBlock [.unreachable] [.nop])] =
    some [instr (.block emptyBlock [.nop])] := rfl
example : reduceControlChoice [instr (.const (.i32 7)),
    instr (.if_ emptyBlock [.nop] [.unreachable])] =
    some [instr (.block emptyBlock [.nop])] := rfl
example : reduceControlChoice [instr (.const (.i32 0)), instr (.brIf 2)] = some [] := rfl
example : reduceControlChoice [instr (.const (.i32 7)), instr (.brIf 2)] =
    some [instr (.br 2)] := rfl
example : reduceControlChoice [instr (.const (.i32 1)), instr (.brTable [4, 6] 8)] =
    some [instr (.br 6)] := rfl
example : reduceControlChoice [instr (.const (.i32 4294967295)),
    instr (.brTable [4, 6] 8)] = some [instr (.br 8)] := rfl
example : reduceControlChoice [instr (.const (.i64 0)), instr (.brIf 2)] = none := rfl
example : reduceControlChoice [instr (.brIf 2)] = none := rfl

#print axioms Wasm.reduceControlChoice_sound

#print axioms Wasm.Step.toExecStep
#print axioms Wasm.Steps.toExecSteps
#print axioms Wasm.ExecSteps.trans
#print axioms Wasm.ExecSteps.inLabel
#print axioms Wasm.ExecSteps.inContext
#print axioms Wasm.SeqTyping.toControlSeqTyping

end Wasm.Tests
