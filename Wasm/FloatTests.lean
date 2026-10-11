import Wasm.NativeExecution
import Wasm.ExecutableValidationSoundness
import Wasm.Text.Float

namespace Wasm.Tests.Floats

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"floats: {message}")

private def literalIs (width : NumWidth) (text : String) (expected : Value) : Bool :=
  match Text.floatLiteral width text with
  | .ok actual => actual == expected
  | .error _ => false

private def floatModule : Module := {
  types := [.func ⟨[.f32], [.f32]⟩, .func ⟨[], [.f64]⟩, .func ⟨[], [.i32]⟩]
  globals := [⟨⟨.var, .f32⟩, [.const (.f32 0)]⟩]
  mems := [⟨.i32, 1, none⟩]
  funcs := [
    ⟨0, [.f64], [.localGet 0, .floatUnary .w32 .sqrt, .const (.f32 0),
      .floatBinary .w32 .add, .globalSet 0, .globalGet 0]⟩,
    ⟨1, [], [.const (.f32 0), .floatConvert .promote]⟩,
    ⟨2, [], [.const (.i32 0), .load .f32 0 ⟨2, 0⟩,
      .const (.f32 0), .floatRel .w32 .eq]⟩] }

private theorem floatModule_valid : floatModule.Valid := Validation.validate_sound (by
  have h : (Validation.validate floatModule).isOk = true := by decide +kernel
  cases he : Validation.validate floatModule with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok payload => cases payload; rfl)

#eval do
  check ((Validation.validate floatModule).isOk) "float validation"
  check ((Validation.validate {floatModule with funcs := [
    ⟨1, [], [.unreachable, .select none]⟩]}).isOk) "polymorphic float select"
  let code := values [.f32 0x3f800000, .f32 0x3f800000] ++
    instructions [.floatBinary .w32 .add]
  let config : Configuration := ⟨{}, {}, code⟩
  check ((runConfiguration 10 config).status == RunStatus.stuck)
    "certified runner excludes arithmetic"
  check ((Native.run 10 config).status == RunStatus.finished [.f32 0x40000000])
    "native float runner"
  check ((Native.run 0 config).status == RunStatus.exhausted) "native fuel exhaustion"
  check ((Native.run 10 ⟨{}, {}, values [.f64 0x7ff8000000000000] ++
    instructions [.floatConvert (.trunc .w32 .w64 true false)]⟩).status == RunStatus.trapped)
    "truncation NaN trap"
  check (Native.evalUnary .w32 .neg (.f32 0x7f800001) == some (Value.f32 0xff800001))
    "negation preserves signaling NaN payload"
  check (literalIs .w32 "0x1p-149" (.f32 1)) "smallest f32 subnormal"
  check (literalIs .w64 "0x1p-1074" (.f64 1)) "smallest f64 subnormal"
  check (literalIs .w32 "0x1.000001p0" (.f32 0x3f800000)) "rounding tie"
  check (literalIs .w32 "0x1.000003p0" (.f32 0x3f800002)) "odd rounding tie"
  for literal in ["nan:0x0", "nan:0x800000", "1e999999999", "1__0", "1e", "0x1p+"] do
    check (!(Text.floatLiteral .w32 literal).isOk) "invalid float literal"
  check (literalIs .w32 "-1e-999999999" (.f32 0x80000000))
    "underflow preserves zero sign"

#print axioms floatModule_valid
#print axioms Validation.validate_sound
#print axioms runConfiguration_sound

end Wasm.Tests.Floats
