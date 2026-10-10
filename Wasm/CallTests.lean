import Wasm.Configuration
import Wasm.CallValidation

namespace Wasm.Tests

open AdminInstr

private def checkCall (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"call regression failed: {name}")
private def sameCall {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameCall

#eval do
  let pairType : FuncType := ⟨[.i32, .i64], [.i64, .i32]⟩
  let owner : ModuleInst := { types := [pairType], funcs := [⟨0⟩] }
  let pair : FuncInst := ⟨pairType, owner,
    .wasm ⟨0, [], [.localGet 1, .localGet 0]⟩⟩
  let store : Store := { funcs := [pair] }
  let caller : Frame := { locals := [some (.i32 99)], module := owner }
  let input := values [.i32 42, .i32 3, .i64 4] ++ [instr (.call 0), instr .nop]
  let config : Configuration := ⟨store, caller, input⟩
  let lowered := values [.i32 42, .i32 3, .i64 4] ++
    [AdminInstr.invoke ⟨0⟩ pairType, instr .nop]
  checkCall "exact direct lowering" (stepConfiguration config ≟
    some ⟨store, caller, lowered⟩)
  let callee := Frame.initialize owner [.i32 3, .i64 4] []
  -- Check entry explicitly rather than relying only on final output.
  checkCall "argument transfer" (stepCalls store caller lowered ≟ some
    (values [.i32 42] ++ [AdminInstr.frame 2 callee
      [.label 2 [] (instructions [.localGet 1, .localGet 0])], instr .nop]))
  let result := runConfiguration 30 config
  checkCall "multi parameters/results and caller operands"
    (result.status ≟ .finished [.i32 42, .i64 4, .i32 3])
  checkCall "caller frame restored" (result.state.frame ≟ caller)
  checkCall "store preserved" (result.state.store ≟ store)
  checkCall "fuel counts lowering" ((runConfiguration 1 config).state.code ≟ lowered)
  checkCall "zero fuel call" ((runConfiguration 0 config).status ≟ .exhausted)
  checkCall "resume" ((runConfiguration 30 (runConfiguration 2 config).state).status ≟
    result.status)
  checkCall "missing module index" ((runConfiguration 10
    ⟨store, caller, [instr (.call 1)]⟩).status ≟ .stuck)
  let dangling : Frame := { module := { funcs := [⟨7⟩] } }
  checkCall "missing store address" ((runConfiguration 10
    ⟨store, dangling, [instr (.call 0)]⟩).status ≟ .stuck)
  checkCall "call underflow" ((runConfiguration 10
    ⟨store, caller, [instr (.call 0)]⟩).status ≟ .stuck)
  checkCall "wrong argument types" ((runConfiguration 10
    ⟨store, caller, values [.i64 3, .i32 4] ++ [instr (.call 0)]⟩).status ≟ .stuck)
  checkCall "mismatched invocation signature"
    (stepCalls store caller [.invoke ⟨0⟩ ⟨[], []⟩] ≟ none)
  let host : FuncInst := ⟨pairType, {}, .host 0⟩
  checkCall "host execution remains unsupported" ((runConfiguration 10
    ⟨{ funcs := [host] }, caller, input⟩).status ≟ .stuck)
  let invalid : FuncInst := { pair with module := {} }
  checkCall "invalid callee signature" ((runConfiguration 10
    ⟨{ funcs := [invalid] }, caller, input⟩).status ≟ .stuck)
  let mutate : FuncInst := { pair with code := .wasm ⟨0, [.i32],
    [.const (.i32 8), .localSet 0, .localGet 1, .localGet 2]⟩ }
  checkCall "callee writes and default locals" ((runConfiguration 30
    ⟨{ funcs := [mutate] }, caller, instructions [.const (.i32 3), .const (.i64 4), .call 0,
      .localGet 0]⟩).status ≟ .finished [.i64 4, .i32 0, .i32 99])
  checkCall "call cannot borrow activation operands" ((runConfiguration 15
    ⟨store, caller, values [.i32 3, .i64 4] ++
      [AdminInstr.frame 2 caller [instr (.call 0)]]⟩).status ≟ .stuck)
  checkCall "zero fuel finished" ((runConfiguration 0
    ⟨store, caller, values [.i32 7]⟩).status ≟ .finished [.i32 7])
  checkCall "zero fuel trapped" ((runConfiguration 0 ⟨store, caller, [.trap]⟩).status ≟ .trapped)
  checkCall "zero fuel stuck" ((runConfiguration 0
    ⟨store, caller, [instr .return_]⟩).status ≟ .stuck)

  let retType : FuncType := ⟨[], [.i32]⟩
  let defModule : ModuleInst := { types := [retType], funcs := [⟨1⟩] }
  let wrapper : FuncInst := ⟨retType, defModule, .wasm ⟨0, [], [.call 0]⟩⟩
  let target : FuncInst := ⟨retType, defModule, .wasm ⟨0, [], [.const (.i32 7)]⟩⟩
  let importer : Frame := { module := { funcs := [⟨0⟩] } }
  checkCall "imported callee resolves in defining module" ((runConfiguration 30
    ⟨{ funcs := [wrapper, target] }, importer, [instr (.call 0)]⟩).status ≟ .finished [.i32 7])
  let early : FuncInst := ⟨retType, defModule, .wasm ⟨0, [.i32],
    [.block (.val none) [.block (.val none)
      [.const (.i64 123), .const (.i32 9), .return_, .unreachable]], .unreachable]⟩⟩
  checkCall "nested return discards operands and suffix" ((runConfiguration 30
    ⟨{ funcs := [early] }, importer, [instr (.call 0)]⟩).status ≟ .finished [.i32 9])
  checkCall "return label exact step" (step []
    [.label 0 [.nop] (values [.i64 2, .i32 9] ++ [instr .return_, instr .unreachable])] ≟
    some (values [.i64 2, .i32 9] ++ [instr .return_]))
  checkCall "return frame exact step" (step []
    [.frame 1 {} (values [.i64 2, .i32 9] ++ [instr .return_, instr .unreachable])] ≟
    some (values [.i32 9]))
  checkCall "void return" ((run 10 [] [.frame 0 {}
    (values [.i64 2] ++ [instr .return_, instr .unreachable])]).status ≟ .finished [])
  checkCall "return outside function" ((run 10 [] [instr .return_]).status ≟ .stuck)
  checkCall "return underflow" ((run 10 [] [.frame 1 {} [instr .return_]]).status ≟ .stuck)
  checkCall "multi result return" ((run 10 [] [.frame 2 {}
    (values [.i32 1, .i64 2, .i32 3] ++ [instr .return_])]).status ≟
    .finished [.i64 2, .i32 3])
  checkCall "nearest activation" ((run 20 [] [.frame 1 {}
    [.frame 1 {} (instructions [.const (.i32 9), .return_, .unreachable]),
      instr (.const (.i32 1)), instr (.binop .i32 .add)]]).status ≟ .finished [.i32 10])
  let trapper : FuncInst := { target with code := .wasm ⟨0, [], [.unreachable]⟩ }
  checkCall "callee trap" ((runConfiguration 20
    ⟨{ funcs := [trapper] }, importer, [instr (.call 0), instr .unreachable]⟩).status ≟ .trapped)
  let voidType : FuncType := ⟨[], []⟩
  let voidModule : ModuleInst := { types := [voidType], funcs := [⟨0⟩] }
  let voidFunc : FuncInst := ⟨voidType, voidModule, .wasm ⟨0, [], [.return_]⟩⟩
  checkCall "void call and suffix" ((runConfiguration 20
    ⟨{ funcs := [voidFunc] }, { module := voidModule }, instructions [.call 0, .const (.i64 5)]⟩).status ≟
    .finished [.i64 5])
  let forever : FuncInst := { voidFunc with code := .wasm ⟨0, [], [.call 0]⟩ }
  checkCall "recursive divergence is fuel bounded" ((runConfiguration 40
    ⟨{ funcs := [forever] }, { module := voidModule }, [instr (.call 0)]⟩).status ≟ .exhausted)
  let factType : FuncType := ⟨[.i32], [.i32]⟩
  let factModule : ModuleInst := { types := [factType], funcs := [⟨0⟩] }
  let fact : FuncInst := ⟨factType, factModule, .wasm ⟨0, [],
    [.localGet 0, .eqz .i32, .if_ (.val (some .i32))
      [.const (.i32 1), .return_]
      [.localGet 0, .localGet 0, .const (.i32 1), .binop .i32 .sub,
        .call 0, .binop .i32 .mul, .return_]]⟩⟩
  checkCall "recursive factorial" ((runConfiguration 200
    ⟨{ funcs := [fact] }, { module := factModule }, instructions [.const (.i32 5), .call 0]⟩).status ≟
    .finished [.i32 120])
  let mutualModule : ModuleInst := { types := [factType], funcs := [⟨0⟩, ⟨1⟩] }
  let countdown (other : Nat) : FuncInst := ⟨factType, mutualModule, .wasm ⟨0, [],
    [.localGet 0, .eqz .i32, .if_ (.val (some .i32)) [.const (.i32 0)]
      [.localGet 0, .const (.i32 1), .binop .i32 .sub, .call other]]⟩⟩
  checkCall "mutual recursion" ((runConfiguration 200
    ⟨{ funcs := [countdown 1, countdown 0] }, { module := mutualModule },
      instructions [.const (.i32 7), .call 0]⟩).status ≟ .finished [.i32 0])

example : RuntimeInstrTyping { funcs := [⟨[.i32], [.i64]⟩] } []
    (.call 0) [.i32] [.i64] := .call (ft := ⟨[.i32], [.i64]⟩) rfl
example : RuntimeInstrTyping { returns := some [.i32] } []
    .return_ [.i64, .i32] [.i64] := .return_ (input := [.i64]) rfl
example : RuntimeInstrTyping { returns := some [] } [] .return_ [] [] :=
  .return_ (input := []) rfl
example : RuntimeInstrTyping { returns := some [.i32] } []
    (.block (.val (some .i32)) [.const (.i32 9), .return_]) [] [.i32] :=
  .block (ft := ⟨[], [.i32]⟩) rfl
    (.cons (.plain (.plain (.plain .const)))
      (.cons (.return_ (input := []) rfl) .empty))

example : FuncTyping [⟨[.i32], [.i32]⟩] [⟨[.i32], [.i32]⟩] [] [] 0
    ⟨0, [], [.localGet 0, .call 0, .return_]⟩ ⟨[.i32], [.i32]⟩ :=
  .wasm rfl (by decide) (.cons (.plain (.localGet rfl))
    (.cons (.call (ft := ⟨[.i32], [.i32]⟩) rfl)
      (.cons (.return_ (input := []) rfl) .empty)))

#print axioms stepCalls_sound
#print axioms FuncInst.activation?_sound
#print axioms FuncInst.activation?_complete
#print axioms runConfiguration_sound
#print axioms runConfiguration_finished
#print axioms runConfiguration_trapped
#print axioms ConfigSteps.functions_preserved

end Wasm.Tests
