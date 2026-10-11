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

-- Native hooks retain the same machine through fuel exhaustion and context unwinding.
#eval do
  let body := values [.i32 42] ++ [AdminInstr.invoke ⟨1⟩ ⟨[.i32], []⟩]
  let config : Configuration := ⟨{Spectest.store with mems := [], tables := []}, {},
    [.frame 0 {} [.label 0 [] [.handler [] body]]]⟩
  let machine := Fast.Machine.ofConfiguration (Fast.Configuration.ofSpec config)
  let first := Native.runMachine 1 machine
  check (first.status == RunStatus.exhausted && first.output == [Value.i32 42])
    "host output belongs to its semantic step before unwinding"
  let resumed := Native.runMachine 100 first.state
  let complete := Native.runMachine 101 machine
  check (resumed.status == RunStatus.finished [] && resumed.output.isEmpty)
    "resuming must unwind without repeating host output"
  check (resumed.state.toSpec == complete.state.toSpec &&
    first.output ++ resumed.output == complete.output)
    "native machine fuel composition and output ordering"
  let probe := Native.runMachine 0 machine
  check (probe.status == RunStatus.exhausted && probe.output.isEmpty && probe.state == machine)
    "native status probing must neither advance nor emit output"

end Wasm.SpectestTests
