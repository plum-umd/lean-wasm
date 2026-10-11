import Wasm.TypeSafety.CoreTests
import Wasm.TypeSafety.NativeTests

namespace Wasm.Tests.TypeSafety

example (a b : BitVec 32) (op : IntBinOp) :
    ∃ result, Reduces [.instr (.const (.i32 a)), .instr (.const (.i32 b)),
      .instr (.binop .i32 op)] (values [result]) ∧ result.type = .i32 :=
  Wasm.TypeSafety.binop_progress (by trivial) rfl rfl

example (a b : BitVec 64) (op : IntBinOp) :
    ∃ result, Reduces [.instr (.const (.i64 a)), .instr (.const (.i64 b)),
      .instr (.binop .i64 op)] (values [result]) ∧ result.type = .i64 :=
  Wasm.TypeSafety.binop_progress (by trivial) rfl rfl

example (a : BitVec 64) :
    ∃ result, Reduces [.instr (.const (.i64 a)), .instr (.eqz .i64)] (values [result]) ∧
      result.type = .i32 :=
  Wasm.TypeSafety.eqz_progress (by trivial) rfl

open Wasm.TypeSafety

-- The theorem applies to arbitrary operands, stores, frames, and execution lengths.
example (config next : Configuration) (output : List ValType)
    (typed : FlatTyping config.code [] output) (supported : ScalarCode config.code)
    (steps : ConfigSteps config next) :
    FlatTyping next.code [] output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) :=
  flat_configuration_safety typed supported steps

example (a b : BitVec 64) (op : IntBinaryOp) :
    ∃ result : NumericResult,
      IntegerReduces [.instr (.const (.i64 a)), .instr (.const (.i64 b)),
        .instr (.intBinary .i64 op)] result.code ∧ NumericResultTyped result .i64 :=
  binary_progress (by trivial) rfl rfl

example (source : List Instr) (output : List ValType)
    (typed : SeqTyping source [] output) (supported : ScalarCode (instructions source))
    (config : Configuration) (code : config.code = instructions source) :
    FlatTerminal config.code ∨ ∃ next, ConfigStep config next := by
  apply flat_configuration_progress (output := output)
  · rw [code]; exact SeqTyping.toFlatTyping typed
  · simpa [code] using supported

#print axioms Wasm.TypeSafety.binary_progress
#print axioms Wasm.TypeSafety.ConfigStep.preserves_flat
#print axioms Wasm.TypeSafety.flat_configuration_progress
#print axioms Wasm.TypeSafety.flat_configuration_safety
#print axioms Wasm.TypeSafety.flat_configuration_results
#print axioms Wasm.TypeSafety.runConfiguration_flat_safe

#print axioms Wasm.TypeSafety.binop_progress
#print axioms Wasm.TypeSafety.binop_preservation
#print axioms Wasm.TypeSafety.eqz_progress
#print axioms Wasm.TypeSafety.eqz_preservation

end Wasm.Tests.TypeSafety
