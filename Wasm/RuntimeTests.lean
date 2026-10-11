import Wasm.Configuration

namespace Wasm.Tests

open AdminInstr

private def checkRuntime (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"runtime regression failed: {name}")

private def sameRuntime {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameRuntime

#eval do
  let signature : FuncType := ⟨[.i32], [.i64]⟩
  let owner : ModuleInst :=
    { types := [signature], funcs := [⟨0⟩], exports := [⟨"f", .func ⟨0⟩⟩] }
  let function : FuncInst := ⟨signature, owner, .wasm ⟨0, [.i64, .i32], [.const (.i64 7)]⟩⟩
  let host : FuncInst := ⟨signature, {}, .host 42⟩
  let store : Store := { funcs := [function, host] }
  let importer : ModuleInst := { funcs := [⟨1⟩, ⟨0⟩] }
  checkRuntime "index differs from address" (store.resolveFunc? importer 0 ≟ some host)
  checkRuntime "import retains defining module" (store.resolveFunc? importer 1 ≟ some function)
  checkRuntime "missing index" (store.resolveFunc? importer 2 ≟ none)
  checkRuntime "missing address" (store.func? ⟨2⟩ ≟ none)
  checkRuntime "self address" (store.resolveFunc? owner 0 ≟ some function)
  checkRuntime "export" (owner.export? "f" ≟ some (.func ⟨0⟩))
  checkRuntime "missing export" (owner.export? "g" ≟ none)
  let allocated := store.allocateFunc function
  checkRuntime "allocation address" (allocated.1 ≟ ⟨2⟩)
  checkRuntime "allocation lookup" (allocated.2.func? allocated.1 ≟ some function)
  checkRuntime "allocation preserves" (allocated.2.func? ⟨0⟩ ≟ some function)
  let state := Frame.initialize owner [.i32 9] [.i64, .i32]
  checkRuntime "parameter and default local order"
    (state.locals ≟ [some (.i32 9), some (.i64 0), some (.i32 0)])
  checkRuntime "empty frame" ((Frame.initialize {} [] []).locals ≟ [])
  checkRuntime "wrong argument width" (function.activation? [.i64 9] ≟ none)
  checkRuntime "missing argument" (function.activation? [] ≟ none)
  checkRuntime "host activation unavailable" (host.activation? [.i32 9] ≟ none)
  let invalid : FuncInst := { function with module := {} }
  checkRuntime "missing signature" (invalid.activation? [.i32 9] ≟ none)
  let activation := function.activation? [.i32 9]
  checkRuntime "activation shape" (activation ≟ some
    (.frame 1 state [.label 1 [] (instructions [.const (.i64 7)])]))
  match activation with
  | none => throw (IO.userError "expected activation")
  | some code => checkRuntime "activation execution" ((run 10 [] [code]).status ≟ .finished [.i64 7])
  checkRuntime "zero results" ((run 10 [] [.frame 0 {} []]).status ≟ .finished [])
  checkRuntime "multiple results" ((run 10 [] [.frame 2 {} (values [.i32 1, .i64 2])]).status ≟
    .finished [.i32 1, .i64 2])
  checkRuntime "return arity mismatch" ((run 10 [] [.frame 1 {} []]).status ≟ .stuck)
  checkRuntime "frame trap" ((run 10 [] [.frame 0 {} [instr .unreachable]]).status ≟ .trapped)
  checkRuntime "isolated operand stack" ((run 10 []
    (values [.i32 1] ++ [AdminInstr.frame 0 {} [instr .drop]])).status ≟ .stuck)
  checkRuntime "branch cannot cross activation" ((run 10 []
    [.label 0 [] [.frame 0 {} [instr (.br 0)]]]).status ≟ .stuck)
  let inner : Frame := { module := { types := [.func ⟨[], [.i32]⟩] } }
  let body := instructions [.block (.typeIdx 0) [.const (.i32 8)]]
  checkRuntime "callee type context" ((run 10 [] [.frame 1 inner body]).status ≟ .finished [.i32 8])
  checkRuntime "nested frame contexts" ((run 15 [] [.frame 1 {} [.frame 1 inner body]]).status ≟
    .finished [.i32 8])
  let config : Configuration := ⟨store, inner, body⟩
  checkRuntime "configuration step" (stepConfiguration config ≟ some
    ⟨store, inner, [.label 1 [] (instructions [.const (.i32 8)])]⟩)

#print axioms Frame.initialize_types
#print axioms Store.allocateFunc_lookup
#print axioms Store.allocateFunc_preserves
#print axioms stepConfiguration_sound

end Wasm.Tests
