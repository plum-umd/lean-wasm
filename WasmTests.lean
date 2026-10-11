import Wasm.VectorTests
import Wasm.GCReferenceTests
import Wasm.TypeAlgorithmTests
import Wasm.BinaryTests
import Wasm.SpectestTests
import Wasm.FloatTests
import Wasm.ExecutableValidationTests
import Wasm.TextTests
import Wasm.ElementInstantiationTests
import Wasm.TypeTests
import Wasm.TypedRuntimeTests
import Wasm.TableTests
import Wasm.RuntimeTests
import Wasm.LocalTests
import Wasm.CallTests
import Wasm.GlobalTests
import Wasm.MemoryTests
import Wasm.BulkMemoryTests
import Wasm.InstantiationTests
import Wasm
import Wasm.ControlTests
import Wasm.StepperTests
import Wasm.IntegerTests

namespace Wasm.Tests

open AdminInstr Instr

-- Kernel-checked examples cover overflow, operand order, widths, and stuckness.
example : evalBinOp .i32 .add (.i32 4294967295) (.i32 1) = some (.i32 0) := by decide
example : evalBinOp .i32 .sub (.i32 0) (.i32 1) = some (.i32 4294967295) := by decide
example : evalBinOp .i64 .add (.i64 18446744073709551615) (.i64 1) =
    some (.i64 0) := by decide
example : evalBinOp .i32 .mul (.i32 2147483648) (.i32 2) = some (.i32 0) := by decide
example : evalEqz .i64 (.i64 0) = some (.i32 1) := by decide
example : evalEqz .i64 (.i64 5) = some (.i32 0) := by decide
example : reduce [instr (.const (.i32 9)), instr (.const (.i32 4)),
    instr (.binop .i32 .sub)] = some [instr (.const (.i32 5))] := rfl
example : reduce [instr (.const (.i64 7)), instr (.const (.i64 8)),
    instr (.const (.i32 0)), instr (.select none)] =
    some [instr (.const (.i64 8))] := rfl
example : reduce [instr (.const (.i64 7)), instr (.const (.i64 8)),
    instr (.const (.i32 2)), instr (.select (some [.i64]))] =
    some [instr (.const (.i64 7))] := rfl
example : reduce [instr .unreachable] = some [.trap] := rfl
example : reduce [instr .drop] = none := rfl
example : reduce [instr (.const (.i32 0)), instr (.const (.i64 1)),
    instr (.binop .i32 .add)] = none := rfl

example : Step [instr (.const (.i32 42)), instr .nop, instr .drop]
    [instr (.const (.i32 42)), instr .drop] :=
  .context (vs := [.i32 42]) (tail := [instr .drop]) .nop

example : Step [instr (.const (.i32 42)), .trap, instr .drop] [.trap] :=
  .trap (vs := [.i32 42]) (tail := [instr .drop]) (by intro h; cases h)

example : SeqTyping [.const (.i32 9), .const (.i32 4), .binop .i32 .sub] [] [.i32] :=
  .cons .const (.cons (.weaken (ts₀ := [.i32]) .const) (.cons .binop .empty))

example : Steps [instr (.const (.i32 42)), instr (.const (.i32 9)),
    instr (.const (.i32 4)), instr (.binop .i32 .sub), instr .drop]
    [instr (.const (.i32 42))] :=
  .cons (.context (vs := [.i32 42]) (tail := [instr .drop])
    (.binop (result := .i32 5) (by decide)))
    (.cons (.context (vs := [.i32 42]) (tail := []) .drop) .refl)

#print axioms Wasm.reduce_sound
#print axioms Wasm.reduce_complete
#print axioms Wasm.reduces_deterministic
#print axioms Wasm.evalIntBinOp_spec

end Wasm.Tests
