import Wasm.ExecutableValidationSoundness
import Wasm.GCStorage
import Wasm.ConstantExpression

namespace Wasm.Tests.GCReferences

example : Types.StorageType.i8.packValue (.i32 511) = some (.i32 255) := by decide +kernel
example : Types.StorageType.i16.packValue (.i32 131071) = some (.i32 65535) := by
  decide +kernel
example : Types.StorageType.i8.unpackValue (some true) (.i32 128) =
    some (.i32 4294967168) := by decide +kernel
example : Types.StorageType.i16.unpackValue (some true) (.i32 32768) =
    some (.i32 4294934528) := by decide +kernel
example : Types.StorageType.i8.unpackValue none (.i32 0) = none := rfl

private def structureType : Types.DefinedType := ⟨[.struct_ true [] []], 0⟩
private def arrayType : Types.DefinedType := ⟨[.array true [] (.mk .i8 true)], 0⟩

example : RefValue.type? {structs := [⟨structureType, []⟩]} (.struct_ ⟨0⟩) =
    some (.refNonNull structureType.heap) := rfl
example : RefValue.type? {arrays := [⟨arrayType, #[]⟩]} (.array ⟨0⟩) =
    some (.refNonNull arrayType.heap) := rfl
example : RefValue.type? {} (.struct_ ⟨0⟩) = none := rfl
example : RefValue.type? {} (.array ⟨0⟩) = none := rfl

private def execute (code : List Instr) : RunStatus :=
  (runConfiguration 40 ⟨{}, {}, instructions code⟩).status

#eval show IO Unit from do
  let cases : List (List Instr × RunStatus) := [
    ([.const (.i32 4294967295), .gcReference .i31New, .gcReference .i31GetS],
      .finished [.i32 4294967295]),
    ([.const (.i32 4294967295), .gcReference .i31New, .gcReference .i31GetU],
      .finished [.i32 2147483647]),
    ([.const (.i32 2147483648), .gcReference .i31New, .gcReference .i31GetU],
      .finished [.i32 0]),
    ([.refNull .i31, .gcReference .i31GetS], .trapped),
    ([.refNull .any, .refTest true .i31], .finished [.i32 1]),
    ([.refNull .any, .refTest false .i31], .finished [.i32 0]),
    ([.refNull .any, .refCast false .i31], .trapped),
    ([.const (.i32 7), .gcReference .i31New, .refCast false .i31],
      .finished [.ref (.i31 7)]),
    ([.refNull .struct_, .refNull .array, .gcReference .eq], .finished [.i32 1]),
    ([.const (.i32 7), .gcReference .i31New, .gcReference .externConvertAny,
      .gcReference .anyConvertExtern], .finished [.ref (.i31 7)]),
    ([.const (.ref (.extern 17)), .gcReference .anyConvertExtern,
      .gcReference .externConvertAny], .finished [.ref (.extern 17)]),
    ([.block (.val (some (.refNonNull .i31)))
        [.const (.i32 7), .gcReference .i31New,
          .brOnCast false 0 ⟨false, .any⟩ ⟨false, .i31⟩, .unreachable],
      .gcReference .i31GetU], .finished [.i32 7]),
    ([.block (.val (some (.refNonNull .any)))
        [.const (.i32 7), .gcReference .i31New,
          .brOnCast true 0 ⟨false, .any⟩ ⟨false, .struct_⟩, .unreachable],
      .refCast false .i31, .gcReference .i31GetU], .finished [.i32 7])]
  for (code, expected) in cases do
    unless execute code == expected do
      throw (IO.userError s!"certified GC reference execution: {repr code}")

example : (Validation.validate {
    types := [.func ⟨[.refNonNull .extern], [.refNonNull .any]⟩],
    funcs := [⟨0, [], [.localGet 0, .gcReference .anyConvertExtern]⟩] }).isOk = true := by
  decide +kernel

example : (Validation.validate {
    types := [.func ⟨[.ref .extern], [.refNonNull .any]⟩],
    funcs := [⟨0, [], [.localGet 0, .gcReference .anyConvertExtern]⟩] }).isOk = false := by
  decide +kernel

example : Typed {} (.ref (.null .struct_)) (.ref .any) := by
  refine ⟨.ref .none, rfl, ?_⟩
  exact .ref (a := ⟨true, .none⟩) (b := ⟨true, .any⟩)
    ⟨by decide, .none .refl (by intro h; cases h)⟩

#print axioms stepArrays_sound
#print axioms stepStructs_sound
#print axioms stepReferences_sound
#print axioms ConstEval.toConfigSteps
#print axioms Validation.validate_sound

end Wasm.Tests.GCReferences
