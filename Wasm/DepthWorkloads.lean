import Wasm.Workloads

namespace Wasm.Execution.DepthWorkloads

def kinds : List String := ["blocks", "calls", "tail-calls", "handlers", "unwind"]

-- The arithmetic work and heap stay fixed while enclosing context depth varies.
def configuration (kind : String) (iterations depth : Nat) : Wasm.Configuration := Id.run do
  if kind == "calls" || kind == "tail-calls" then
    let signature : FuncType := ⟨[.i32], [.i64]⟩
    let module : ModuleInst :=
      {types := [.func signature], funcs := (List.range (depth + 1)).map FuncAddr.mk}
    let leaf := Workloads.iteration [.localGet 1, .const (.i64 1),
      .binop .i64 .add, .localSet 1] ++ [.localGet 1]
    let functions := (List.range (depth + 1)).map fun index =>
      let body := if index == depth then leaf
        else [.localGet 0, if kind == "tail-calls" then .returnCall (index + 1)
          else .call (index + 1)]
      (⟨signature, module, .wasm ⟨0, [.i64], body⟩⟩ : FuncInst)
    return ⟨{funcs := functions}, ⟨[], module⟩,
      instructions [.const (.i32 (BitVec.ofNat 32 iterations)), .call 0]⟩
  let base := Workloads.configuration "control" iterations
  let body := Workloads.iteration [.localGet 2, .const (.i64 1),
    .binop .i64 .add, .localSet 2] ++ [.localGet 2]
  let throwing := kind == "unwind"
  let body := if throwing then body ++ [.drop, .throw_ 0] else body
  let wrapped := (List.range depth).foldl (fun body _ =>
    if kind == "handlers" || throwing then [.tryTable (.val (some .i64)) [] body]
    else [.block (.val (some .i64)) body]) body
  if throwing then
    let signature : FuncType := ⟨[], []⟩
    return ⟨{tags := [⟨signature, signature.definedType⟩]},
      {base.frame with module := {base.frame.module with tags := [⟨0⟩]}},
      instructions wrapped⟩
  return {base with code := instructions wrapped}

def fuel (iterations depth : Nat) : Nat := 40 * iterations + 20 * depth + 100

def expected (kind : String) (iterations : Nat) : RunStatus :=
  if kind == "unwind" then .exception ⟨0⟩
  else .finished [.i64 (BitVec.ofNat 64 iterations)]

end Wasm.Execution.DepthWorkloads
