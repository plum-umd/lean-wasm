import Wasm.Runtime

/-! The reference interpreter's predefined test host. Print calls have no Wasm results;
the native backend records their diagnostic output separately from Wasm results. -/
namespace Wasm.Spectest

def functions : List (String × FuncType) :=
  [("print", ⟨[], []⟩), ("print_i32", ⟨[.i32], []⟩),
   ("print_i64", ⟨[.i64], []⟩), ("print_f32", ⟨[.f32], []⟩),
   ("print_f64", ⟨[.f64], []⟩), ("print_i32_f32", ⟨[.i32, .f32], []⟩),
   ("print_f64_f64", ⟨[.f64, .f64], []⟩)]

def store : Store :=
  { funcs := functions.zipIdx.map fun ((_, type), id) =>
      ⟨type, {}, .hostTyped id type.definedType⟩
    globals := [⟨⟨.const, .i32⟩, .i32 666⟩, ⟨⟨.const, .i64⟩, .i64 666⟩,
      ⟨⟨.const, .f32⟩, .f32 (BitVec.ofNat 32 0x4426a666)⟩,
      ⟨⟨.const, .f64⟩, .f64 (BitVec.ofNat 64 0x4084d4cccccccccd)⟩]
    mems := [⟨⟨.i32, 1, some 2⟩, Array.replicate 65536 0⟩]
    tables := [⟨⟨.i32, 10, some 20, .func, true⟩, Array.replicate 10 (.null .func)⟩,
      ⟨⟨.i64, 10, some 20, .func, true⟩, Array.replicate 10 (.null .func)⟩] }

def module : ModuleInst :=
  { funcs := (List.range functions.length).map FuncAddr.mk
    globals := (List.range 4).map GlobalAddr.mk
    mems := [⟨0⟩]
    tables := [⟨0⟩, ⟨1⟩]
    exports := (functions.zipIdx.map fun ((name, _), id) => ⟨name, .func ⟨id⟩⟩) ++
      [⟨"global_i32", .global ⟨0⟩⟩, ⟨"global_i64", .global ⟨1⟩⟩,
       ⟨"global_f32", .global ⟨2⟩⟩, ⟨"global_f64", .global ⟨3⟩⟩,
       ⟨"memory", .memory ⟨0⟩⟩, ⟨"table", .table ⟨0⟩⟩, ⟨"table64", .table ⟨1⟩⟩] }

/-- Recognize only the seven declared host handles with their exact closed signatures. -/
def accepts (function : FuncInst) : Bool :=
  match function.code with
  | .hostTyped id type => match functions[id]? with
    | some (_, expected) => function.type == expected && type == expected.definedType
    | none => false
  | _ => false

end Wasm.Spectest
