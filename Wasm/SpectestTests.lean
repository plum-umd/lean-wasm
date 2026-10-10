import Wasm.Text.Script

namespace Wasm.SpectestTests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

#eval do
  let config : Configuration := ⟨Spectest.store, {},
    values [.i32 42] ++ [AdminInstr.invoke ⟨1⟩ ⟨[.i32], []⟩]⟩
  check ((runConfiguration 10 config).status == RunStatus.stuck)
    "certified runner must retain the host boundary"
  let result := Native.run 10 config
  check (result.status == RunStatus.finished [] && result.output == [Value.i32 42])
    "native host result and print trace"
  check ((Native.run 0 config).output.isEmpty) "exhaustion must not print speculatively"
  let wrong : Configuration := ⟨Spectest.store, {},
    values [.i64 42] ++ [AdminInstr.invoke ⟨1⟩ ⟨[.i32], []⟩]⟩
  check ((Native.run 10 wrong).status == RunStatus.stuck &&
    (Native.run 10 wrong).output.isEmpty) "wrong host arguments must not print"
  let unknown : Store := {funcs := [⟨⟨[], []⟩, {}, .hostTyped 999 (⟨[], []⟩ : FuncType).definedType⟩]}
  check ((Native.run 10 ⟨unknown, {}, [AdminInstr.invoke ⟨0⟩ ⟨[], []⟩]⟩).status == RunStatus.stuck)
    "arbitrary host handles must not be executed"

end Wasm.SpectestTests
