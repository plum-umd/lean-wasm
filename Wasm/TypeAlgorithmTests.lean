import Wasm.ExecutableValidationSoundness
import Wasm.Configuration

namespace Wasm.Tests.TypeAlgorithms

private def groups : List Types.RecType := [
  [.func false [] [.ref false .func] [.ref true .extern]],
  [.func true [.typeIdx 0] [.ref true .func] [.ref false .noextern]]]

example : Types.Algorithm.typeSection [] groups = true := by decide +kernel

example : ∃ final, Types.resolveSection? [] groups = some final ∧
    Types.TypeSectionValid [] groups final :=
  Types.Algorithm.typeSection_sound (by decide +kernel)

example : Types.Algorithm.typeSection []
    [[.func true [] [] []], [.func true [.typeIdx 0] [] []]] = false := by decide +kernel

example : Types.Algorithm.typeSection []
    [[.func false [] [.ref true .func] []],
      [.func true [.typeIdx 0] [.ref false .func] []]] = false := by decide +kernel

example : Types.Algorithm.typeSection []
    [[.func false [] [] [.i32]], [.func true [.typeIdx 0] [] [.i64]]] = false := by
  decide +kernel

private def recursive : List Types.RecType := [[
  .func true [] [.ref true (.typeIdx 1)] [],
  .func true [] [.ref true (.typeIdx 0)] []]]

example : Types.Algorithm.typeSection [] recursive = true := by decide +kernel

private def module : Module := {
  typeGroups := recursive
  types := [.func ⟨[.ref (.typeIdx 1)], []⟩, .func ⟨[.ref (.typeIdx 0)], []⟩] }

example : module.Valid := Validation.validate_sound (by
  have success : (Validation.validate module).isOk = true := by decide +kernel
  cases checked : Validation.validate module with
  | error error => simp [checked, Except.isOk, Except.toBool] at success
  | ok value => cases value; rfl)

-- Struct width subtyping and immutable field covariance.
private def structGroups : List Types.RecType := [
  [.struct_ false [] [.mk (.val (.ref true .any)) false]],
  [.struct_ true [.typeIdx 0]
    [.mk (.val (.ref false .i31)) false, .mk .i8 true]]]

example : Types.Algorithm.typeSection [] structGroups = true := by decide +kernel

-- Mutable fields require invariant storage types.
example : Types.Algorithm.typeSection [] [
    [.struct_ false [] [.mk (.val (.ref true .any)) true]],
    [.struct_ true [.typeIdx 0] [.mk (.val (.ref false .i31)) true]]] = false := by
  decide +kernel

example : Types.Algorithm.typeSection [] [
    [.array false [] (.mk .i8 true)],
    [.array true [.typeIdx 0] (.mk .i16 true)]] = false := by decide +kernel

example : Types.Algorithm.typeSection [] [[
    .struct_ true [] [.mk (.val (.ref true (.typeIdx 1))) false],
    .array true [] (.mk (.val (.ref true (.typeIdx 0))) false)]] = true := by
  decide +kernel

-- A composite type index must never serve as a function signature.
example : (Validation.validate {
    types := [.struct_ []], typeGroups := [[.struct_ true [] []]],
    funcs := [⟨0, [], []⟩] }).isOk = false := by decide +kernel

private def signature : FuncType := ⟨[], [.i32]⟩
private def owner : ModuleInst := {
  types := [signature], definedTypes := [signature.definedType], funcs := [⟨0⟩] }
private def store : Store := {
  funcs := [⟨signature, owner, .wasm ⟨0, [], [.const (.i32 42)]⟩⟩] }

private def execute (code : List Instr) : RunStatus :=
  (runConfiguration 40 ⟨store, ⟨[], owner⟩, instructions code⟩).status

#eval show IO Unit from do
  let cases : List (List Instr × RunStatus) := [
    ([.refFunc 0, .refAsNonNull, .callRef 0], .finished [.i32 42]),
    ([.refNull (.typeIdx 0), .callRef 0], .trapped),
    ([.refNull .extern, .refAsNonNull], .trapped),
    ([.block (.val none) [.refNull .extern, .brOnNull 0, .drop, .unreachable],
      .const (.i32 9)], .finished [.i32 9]),
    ([.block (.val (some (.ref .extern)))
      [.const (.ref (.extern 7)), .brOnNonNull 0, .refNull .extern]],
      .finished [.ref (.extern 7)])]
  for (code, expected) in cases do
    unless execute code == expected do
      throw (IO.userError s!"certified typed-reference execution: {repr code}")

#print axioms Types.Algorithm.heapMatches_sound
#print axioms Types.Algorithm.valMatches_sound
#print axioms Types.Algorithm.typeSection_sound
#print axioms Validation.validate_sound

end Wasm.Tests.TypeAlgorithms
