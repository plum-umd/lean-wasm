import Wasm.Fast.Correspondence

/-! Deterministic configurations shared by differential tests and compiled benchmarks. -/
namespace Wasm.Fast.Workloads

-- A fixed-size immutable payload, and an immutable node with a reference to its predecessor.
def payloadType : Types.DefinedType :=
  ⟨[.struct_ true [] [.mk (.val .i64) false]], 0⟩
def nodeType : Types.DefinedType :=
  ⟨[.struct_ true [] [.mk (.val .i64) false, .mk (.val (.ref true .any)) false]], 0⟩

def object (n : Nat) : StructInst := ⟨payloadType, [.i64 (BitVec.ofNat 64 n)]⟩

def iteration (body : List Instr) : List Instr :=
  [.block (.val none) [.loop (.val none)
    ([.localGet 0, .eqz .i32, .brIf 1] ++ body ++
     [.localGet 0, .const (.i32 1), .binop .i32 .sub, .localSet 0, .br 0])]]

/-- Looping configurations keep code size independent of the workload size. -/
def configuration (kind : String) (n : Nat) : Wasm.Configuration := Id.run do
  let types : TypeContext := [.struct_ [.mk (.val .i64) false],
    .struct_ [.mk (.val .i64) false, .mk (.val (.ref true .any)) false]]
  let module : ModuleInst :=
    { types := types, definedTypes := [payloadType, nodeType], funcs := [⟨0⟩] }
  let frame : Frame := {
    module := module
    locals := [some (.i32 (BitVec.ofNat 32 n)), some (.ref (.null .any)), some (.i64 0)] }
  if kind == "allocate" then
    return ⟨{}, frame, instructions (iteration
      [.const (.i64 7), .structNew 0 false, .drop] ++ [.const (.i64 7)])⟩
  if kind == "allocate-read" then
    return ⟨{}, frame, instructions (iteration
      [.const (.i64 7), .structNew 0 false, .structGet 0 0 none, .localSet 2] ++
      [.localGet 2])⟩
  if kind == "linked" then
    let signature : FuncType := ⟨[.i64, .ref .any], [.refNonNull nodeType.heap]⟩
    let functionModule : ModuleInst :=
      { module with types := types ++ [.func signature] }
    let function : FuncInst := ⟨signature, functionModule,
      .wasm ⟨2, [], [.localGet 0, .localGet 1, .structNew 1 false]⟩⟩
    let build := iteration
      [.const (.i64 1), .localGet 1, .call 0, .localSet 1]
    let walk := iteration
      [.localGet 1, .refCast false nodeType.heap, .structGet 1 0 none,
       .localGet 2, .binop .i64 .add, .localSet 2,
       .localGet 1, .refCast false nodeType.heap, .structGet 1 1 none, .localSet 1]
    return ⟨{funcs := [function]}, frame,
      instructions (build ++ [.const (.i32 (BitVec.ofNat 32 n)), .localSet 0] ++
        walk ++ [.localGet 2])⟩
  -- Fixed-heap reads isolate heap lookup from allocation.
  if kind == "read-early" || kind == "read-middle" || kind == "read-late" then
    let index := if kind == "read-early" then 0 else
      if kind == "read-middle" then n / 2 else n - 1
    return ⟨{structs := (List.range n).map object}, frame,
      instructions (iteration [.const (.ref (.struct_ ⟨index⟩)),
        .structGet 0 0 none, .localSet 2] ++ [.localGet 2])⟩
  return ⟨{}, frame, instructions (iteration [.localGet 2, .const (.i64 1),
    .binop .i64 .add, .localSet 2] ++ [.localGet 2])⟩

def fuel (kind : String) (n : Nat) : Nat :=
  (if kind == "linked" then 100 else 30) * n + 100

def expected (kind : String) (n : Nat) : List Value :=
  [.i64 (BitVec.ofNat 64 (if kind == "control" || kind == "linked" then n
    else if kind == "read-early" then 0
    else if kind == "read-middle" then n / 2
    else if kind == "read-late" then n - 1 else 7))]

end Wasm.Fast.Workloads
