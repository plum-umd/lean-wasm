import Wasm.Configuration
import Wasm.NativeVector

namespace Wasm.Tests

private def vector (width : Nat) (lanes : List Nat) : Value :=
  .v128 (BitVec.ofNat 128 (vectorPack width lanes))

example : vectorLane 8 (vectorPack 8 [1, 2, 255]) 2 = 255 := by decide
example : vectorSigned 16 65535 = -1 := by decide
example : vectorSaturate 8 false (-1) = 0 := by decide
example : vectorSaturate 8 true 200 = 127 := by decide

#eval show IO Unit from do
  let check (op : VectorOpcode) (args : List Value) (wanted : Value) := do
    if evalVector {opcode := op} args != some wanted then
      throw (IO.userError s!"SIMD edge case: {op.name}")
  let ones := vector 8 (List.replicate 16 255)
  let twos := vector 8 (List.replicate 16 2)
  check .i8x16_add [ones, twos] (vector 8 (List.replicate 16 1))
  check .i8x16_add_sat_u [ones, twos] ones
  check .i8x16_shr_s [ones, .i32 9] ones
  check .i16x8_q15mulr_sat_s
    [vector 16 (List.replicate 8 32768), vector 16 (List.replicate 8 32768)]
    (vector 16 (List.replicate 8 32767))
  check .i8x16_narrow_i16x8_u
    [vector 16 (List.replicate 8 65535), vector 16 (List.replicate 8 256)]
    (vector 8 (List.replicate 8 0 ++ List.replicate 8 255))
  check .i32x4_dot_i16x8_s
    [vector 16 (List.replicate 8 32768), vector 16 (List.replicate 8 32768)]
    (vector 32 (List.replicate 4 2147483648))
  let op : VectorOp := {opcode := .i8x16_shuffle, lanes := List.replicate 16 32}
  if vectorSignature? [] op != none then throw (IO.userError "invalid shuffle accepted")
  if evalVector op [ones, twos] != none then
    throw (IO.userError "invalid shuffle executed")
  let op : VectorOp := ⟨.v128_load, [], 0, ⟨5, 0⟩⟩
  if vectorSignature? [⟨.i32, 0, none⟩] op != none then
    throw (IO.userError "overaligned vector load accepted")

#eval show IO Unit from do
  let memory : MemoryInst := ⟨⟨.i32, 0, none⟩, Array.replicate 16 0⟩
  let store : Store := {mems := [memory]}
  let frame : Frame := {module := {mems := [⟨0⟩]}}
  let op : VectorOp := {opcode := .v128_load}
  if evalVectorMemory store frame op [.i32 0, .i32 1] != none then
    throw (IO.userError "vector memory redex consumed excess operands")
  if evalVectorMemory store frame op [.i32 0] != some (none, values [.v128 0]) then
    throw (IO.userError "vector load rejected its exact operands")

#print axioms stepVectors_sound
#print axioms vectorSignature?_sound

end Wasm.Tests
