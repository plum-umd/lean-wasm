import Wasm.Configuration
import Wasm.CallValidation

namespace Wasm.Tests

open AdminInstr
private def checkGlobal (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"global regression failed: {name}")
private def sameGlobal {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameGlobal

#eval do
  let g32 : GlobalInst := ⟨⟨.var, .i32⟩, .i32 3⟩
  let g64 : GlobalInst := ⟨⟨.const, .i64⟩, .i64 4⟩
  let module : ModuleInst :=
    { globals := [⟨1⟩, ⟨0⟩], exports := [⟨"counter", .global ⟨0⟩⟩] }
  let frame : Frame := { locals := [some (.i32 99)], module }
  let store : Store := { globals := [g32, g64] }
  let updated : Store := { globals := [{ g32 with value := .i32 9 }, g64] }
  checkGlobal "index differs from address" (store.resolveGlobal? module 0 ≟ some g64)
  checkGlobal "second module index" (store.resolveGlobal? module 1 ≟ some g32)
  checkGlobal "export" (module.export? "counter" ≟ some (.global ⟨0⟩))
  checkGlobal "read immutable i64" (stepGlobals store frame [instr (.globalGet 0)] ≟
    some (store, values [.i64 4]))
  checkGlobal "read mutable i32" (stepGlobals store frame [instr (.globalGet 1)] ≟
    some (store, values [.i32 3]))
  let body := values [.i64 42, .i32 9] ++ [instr (.globalSet 1), instr (.globalGet 1)]
  checkGlobal "top operand and suffix" (stepGlobals store frame body ≟
    some (updated, values [.i64 42] ++ [instr (.globalGet 1)]))
  let result := runConfiguration 10 ⟨store, frame, body⟩
  checkGlobal "set get execution" (result.status ≟ .finished [.i64 42, .i32 9])
  checkGlobal "store update persists" (result.state.store ≟ updated)
  checkGlobal "frame preserved" (result.state.frame ≟ frame)
  checkGlobal "missing module index" (stepGlobals store frame [instr (.globalGet 2)] ≟ none)
  let dangling : Frame := { module := { globals := [⟨3⟩] } }
  checkGlobal "missing store address" (stepGlobals store dangling [instr (.globalGet 0)] ≟ none)
  checkGlobal "set missing index"
    (stepGlobals store frame (instructions [.const (.i32 9), .globalSet 2]) ≟ none)
  checkGlobal "set missing address"
    (stepGlobals store dangling (instructions [.const (.i32 9), .globalSet 0]) ≟ none)
  checkGlobal "set underflow" (stepGlobals store frame [instr (.globalSet 1)] ≟ none)
  checkGlobal "no skipping instructions"
    (stepGlobals store frame [instr .nop, instr (.globalGet 1)] ≟ none)
  checkGlobal "zero fuel pending global"
    ((runConfiguration 0 ⟨store, frame, [instr (.globalGet 1)]⟩).status ≟ .exhausted)
  checkGlobal "one step write" ((runConfiguration 1 ⟨store, frame, body⟩).state.store ≟ updated)
  checkGlobal "resume" ((runConfiguration 10
    (runConfiguration 1 ⟨store, frame, body⟩).state).status ≟ result.status)
  checkGlobal "trap stops write" ((runConfiguration 10
    ⟨store, frame, instructions [.unreachable, .const (.i32 9), .globalSet 1]⟩).state.store ≟ store)
  let afterTrap := runConfiguration 10
    ⟨store, frame, instructions [.const (.i32 9), .globalSet 1, .unreachable]⟩
  checkGlobal "trap keeps earlier write" (afterTrap.state.store ≟ updated)
  checkGlobal "trap status" (afterTrap.status ≟ .trapped)
  let blockBody := instructions [.block (.val none) [.const (.i32 9), .globalSet 1], .globalGet 1]
  checkGlobal "block shares store"
    ((runConfiguration 15 ⟨store, frame, blockBody⟩).status ≟ .finished [.i32 9])
  let inner : Frame := { module := { globals := [⟨0⟩] } }
  checkGlobal "activation uses own global index map" ((runConfiguration 15
    ⟨store, frame, [.frame 1 inner (instructions [.const (.i32 9), .globalSet 0, .globalGet 0])]⟩
    ).status ≟ .finished [.i32 9])
  checkGlobal "no borrowing activation operands" ((runConfiguration 15
    ⟨store, frame, values [.i32 9] ++ [AdminInstr.frame 0 inner [instr (.globalSet 0)]]⟩
    ).status ≟ .stuck)
  let alias : Frame := { module := { globals := [⟨0⟩, ⟨0⟩] } }
  checkGlobal "aliased imports share instance" ((runConfiguration 10 ⟨store, alias,
    instructions [.const (.i32 9), .globalSet 0, .globalGet 1]⟩).status ≟ .finished [.i32 9])
  -- Reduction assumes validation, which rejects immutable and ill-typed writes.
  checkGlobal "no dynamic mutability trap" (stepGlobals store frame
    (instructions [.const (.i64 8), .globalSet 0]) ≟
    some ({ globals := [g32, { g64 with value := .i64 8 }] }, []))
  let ft : FuncType := ⟨[], []⟩
  let owner : ModuleInst := { types := [ft], globals := [⟨0⟩] }
  let setter : FuncInst := ⟨ft, owner,
    .wasm ⟨0, [], [.const (.i32 9), .globalSet 0, .return_]⟩⟩
  let sharedStore : Store := { funcs := [setter], globals := [g32, g64] }
  let caller : Frame := { module := { funcs := [⟨0⟩], globals := [⟨1⟩, ⟨0⟩] } }
  let acrossCall := runConfiguration 20
    ⟨sharedStore, caller, instructions [.call 0, .globalGet 1]⟩
  checkGlobal "callee updates visible to caller" (acrossCall.status ≟ .finished [.i32 9])
  checkGlobal "callee uses defining global map"
    (acrossCall.state.store.global? ⟨1⟩ ≟ some g64)
  checkGlobal "functions preserved" (acrossCall.state.store.funcs ≟ [setter])
  let trappingSetter : FuncInst :=
    { setter with code := .wasm ⟨0, [], [.const (.i32 9), .globalSet 0, .unreachable]⟩ }
  let failedCall := runConfiguration 20
    ⟨{ funcs := [trappingSetter], globals := [g32, g64] }, caller, [instr (.call 0)]⟩
  checkGlobal "callee trap keeps shared write" (failedCall.state.store.global? ⟨0⟩ ≟
    some { g32 with value := .i32 9 })
  checkGlobal "callee trap propagates" (failedCall.status ≟ .trapped)
  let allocated := sharedStore.allocateGlobal g32
  checkGlobal "global allocation address" (allocated.1 ≟ ⟨2⟩)
  checkGlobal "global allocation lookup" (allocated.2.global? allocated.1 ≟ some g32)
  checkGlobal "global allocation preserves functions" (allocated.2.funcs ≟ sharedStore.funcs)
  checkGlobal "function allocation preserves globals"
    ((sharedStore.allocateFunc setter).2.globals ≟ sharedStore.globals)

example : GlobalInstrTyping [⟨.const, .i64⟩] (.globalGet 0) [] [.i64] :=
  .get (gt := ⟨.const, .i64⟩) rfl
example : GlobalInstrTyping [⟨.var, .i32⟩] (.globalSet 0) [.i32] [] := .set rfl
example : ¬ GlobalInstrTyping [⟨.const, .i32⟩] (.globalSet 0) [.i32] [] :=
  GlobalInstrTyping.immutable_set_rejected rfl
example : RuntimeInstrTyping { globals := [⟨.var, .i32⟩] } []
    (.block (.val (some .i32)) [.globalGet 0]) [] [.i32] :=
  .block (ft := ⟨[], [.i32]⟩) rfl (.cons (.global (.get rfl)) .empty)
example : FuncTyping [⟨[], []⟩] [] [⟨.var, .i32⟩] [] 0
    ⟨0, [], [.const (.i32 9), .globalSet 0, .return_]⟩ ⟨[], []⟩ :=
  .wasm rfl (by decide) (.cons (.plain (.plain (.plain .const)))
    (.cons (.global (.set rfl)) (.cons (.return_ (input := []) rfl) .empty)))

#print axioms stepGlobals_sound
#print axioms GlobalInstrTyping.immutable_set_rejected
#print axioms GlobalStep.functions_preserved
#print axioms GlobalStep.types_preserved
#print axioms ConfigStep.global_types_preserved
#print axioms ConfigSteps.functions_preserved
#print axioms Store.allocateGlobal_preserves

end Wasm.Tests
