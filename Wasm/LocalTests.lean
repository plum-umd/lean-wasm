import Wasm.Configuration
import Wasm.LocalValidation

namespace Wasm.Tests

open AdminInstr
private def checkLocal (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"local regression failed: {name}")
private def sameLocal {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameLocal

#eval do
  let state : Frame := ⟨[some (.i32 3), some (.i64 4), none], {}⟩
  let updated : Frame := { state with locals := [some (.i32 9), some (.i64 4), none] }
  checkLocal "get" (stepLocals state [instr (.localGet 1)] ≟
    some (state, values [.i64 4]))
  checkLocal "get unset" (stepLocals state [instr (.localGet 2)] ≟ none)
  checkLocal "get out of bounds" (stepLocals state [instr (.localGet 3)] ≟ none)
  checkLocal "set" (stepLocals state [instr (.const (.i32 9)), instr (.localSet 0)] ≟
    some (updated, []))
  checkLocal "set initializes" (stepLocals state [instr (.const (.i64 8)), instr (.localSet 2)] ≟
    some ({ state with locals := [some (.i32 3), some (.i64 4), some (.i64 8)] }, []))
  checkLocal "set out of bounds"
    (stepLocals state [instr (.const (.i32 9)), instr (.localSet 3)] ≟ none)
  checkLocal "set underflow" (stepLocals state [instr (.localSet 0)] ≟ none)
  checkLocal "tee exact lowering"
    (stepLocals state [instr (.const (.i32 9)), instr (.localTee 0)] ≟
      some (state, values [.i32 9, .i32 9] ++ [instr (.localSet 0)]))
  checkLocal "tee underflow" (stepLocals state [instr (.localTee 0)] ≟ none)
  checkLocal "tee lowering assumes validation"
    ((stepLocals state [instr (.const (.i32 9)), instr (.localTee 99)]).isSome)
  let code := values [.i64 42, .i32 9] ++ [instr (.localSet 0), instr (.localGet 0)]
  checkLocal "operand order and suffix" (stepLocals state code ≟
    some (updated, values [.i64 42] ++ [instr (.localGet 0)]))
  checkLocal "no skipping instructions"
    (stepLocals state [instr .nop, instr (.localGet 0)] ≟ none)
  let activation := AdminInstr.frame 2 state code
  checkLocal "activation set get" ((run 10 [] [activation]).status ≟
    .finished [.i64 42, .i32 9])
  let teeBody := instructions [.const (.i32 9), .localTee 0, .localGet 0]
  checkLocal "tee roundtrip" ((run 10 [] [.frame 2 state teeBody]).status ≟
    .finished [.i32 9, .i32 9])
  let blockBody := instructions [.block (.val none) [.const (.i32 9), .localSet 0], .localGet 0]
  checkLocal "block shares locals" ((run 15 [] [.frame 1 state blockBody]).status ≟
    .finished [.i32 9])
  let nested : List AdminInstr := [.frame 0 state (instructions [.const (.i32 9), .localSet 0]),
    instr (.localGet 0)]
  checkLocal "nested activation isolates locals"
    ((run 15 [] [.frame 1 state nested]).status ≟ .finished [.i32 3])
  checkLocal "no outer operand borrowing" ((run 10 []
    (values [.i32 9] ++ [AdminInstr.frame 0 state [instr (.localSet 0)]])).status ≟ .stuck)
  checkLocal "trap stops writes" ((run 10 []
    [.frame 0 state (instructions [.unreachable, .const (.i32 9), .localSet 0])]).status ≟ .trapped)
  let config : Configuration := ⟨{}, state, instructions [.const (.i32 9), .localSet 0]⟩
  checkLocal "configuration updates frame" (stepConfiguration config ≟ some ⟨{}, updated, []⟩)

example : FunctionInstrTyping [] [.i32, .i64] [] (.localGet 1) [] [.i64] :=
  .localGet rfl
example : FunctionInstrTyping [] [.i32] [] (.localSet 0) [.i32] [] := .localSet rfl
example : FunctionInstrTyping [] [.i32] [] (.localTee 0) [.i32] [.i32] := .localTee rfl
example : FunctionSeqTyping [] [.i32] [] [.localGet 0, .localSet 0] [] [] :=
  .cons (.localGet rfl) (.cons (.localSet rfl) .empty)
example : FunctionInstrTyping [] [.i32] []
    (.block (.val (some .i32)) [.localGet 0]) [] [.i32] :=
  .block (ft := ⟨[], [.i32]⟩) rfl (.cons (.localGet rfl) .empty)

#print axioms stepLocals_sound
#print axioms LocalStep.module_preserved
#print axioms LocalStep.length_preserved
#print axioms stepConfiguration_sound

end Wasm.Tests
