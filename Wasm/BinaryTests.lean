import Wasm.Text.Script

namespace Wasm.Binary.Tests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"binary: {message}")

private def read (action : DecodeM α) (input : Array UInt8) : Except DecodeError α :=
  (action.run ⟨⟨input⟩, 0, input.size, false⟩).map Prod.fst

private def rejected (result : Except DecodeError α) : Bool :=
  match result with | .error (.malformed _ _) => true | _ => false

#eval do
  check (match read (unsigned 32) #[0x80, 0x80, 0x80, 0x80, 0] with
    | .ok n => n == 0 | _ => false) "nonminimal unsigned LEB"
  check (match read (signed 32) #[0x80, 0x80, 0x80, 0x80, 0x78] with
    | .ok n => n == -2147483648 | _ => false) "signed minimum"
  check (match read (signed 32) #[0xff, 0xff, 0xff, 0xff, 0x7f] with
    | .ok n => n == -1 | _ => false) "nonminimal signed LEB"
  check (rejected (read (unsigned 32) #[0x80, 0x80, 0x80, 0x80, 0x10]))
    "unsigned final byte overflow"
  check (rejected (read (signed 32) #[0x80, 0x80, 0x80, 0x80, 0x08]))
    "signed final byte overflow"
  check (rejected (read (unsigned 32) #[0x80, 0x80, 0x80, 0x80, 0x80, 0]))
    "unsigned excessive representation length"
  check (rejected (read (signed 64) #[0x80])) "truncated signed LEB"
  check (rejected (read (sized (bytes 2)) #[1, 0, 0])) "nested boundary"
  check (rejected (read name #[1, 0xff])) "UTF-8 names"
  let header : Array UInt8 := #[0, 0x61, 0x73, 0x6d, 1, 0, 0, 0]
  for tail in [#[0x0e, 0], #[1, 1, 0, 1, 1, 0], #[5, 2, 0], #[0, 2, 1, 0xff]] do
    check (rejected (decode ⟨header ++ tail⟩)) "malformed section framing or name"
  let gcBytes := header ++ #[1, 11, 3, 0x5f, 0, 0x5e, 0x78, 1,
    0x60, 1, 0x7f, 1, 0x7f, 3, 2, 1, 2,
    10, 10, 1, 8, 0, 0x20, 0, 0xfb, 28, 0xfb, 30, 0x0b]
  let .ok gcModule := decode ⟨gcBytes⟩ | throw (IO.userError "GC module decoding")
  check (gcModule.types ==
    ([.struct_ [], .array (.mk .i8 true), .func ⟨[.i32], [.i32]⟩] : TypeContext))
    "mixed composite types and packed array storage"
  check ((Validation.validate gcModule).isOk) "binary GC reference validation"
  let some function := gcModule.funcs[0]? | throw (IO.userError "missing binary function")
  let status := (runConfiguration 10 ⟨{}, ⟨[some (.i32 4294967295)], {}⟩,
    instructions function.body⟩).status
  check (status == RunStatus.finished [.i32 2147483647]) "certified binary i31 execution"
  let raw := header ++ #[1, 5, 1, 0x60, 0, 1, 0x7c, 3, 2, 1, 0,
    10, 13, 1, 11, 0, 0x44, 1, 0, 0, 0, 0, 0, 0xf8, 0x7f, 0x0b]
  let .ok source := decode ⟨raw⟩ | throw (IO.userError "float module decoding")
  check ((source.funcs.map Func.body) == [[Instr.const (.f64 0x7ff8000000000001)]])
    "float NaN payload bits preserved"
  check ((Validation.validate source).isOk) "binary module shares executable validation"
  let .ok invalid := decode ⟨header ++ #[8, 1, 0]⟩ |
    throw (IO.userError "numeric unknown index must decode")
  check (match Validation.validate invalid with
    | .error (.invalid _) => true | _ => false) "numeric unknown index is validation failure"

end Wasm.Binary.Tests
