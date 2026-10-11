import Wasm.NativeFloat
import Wasm.Vectors

namespace Wasm.Native

private def vectorFloatUnary? : String → Option FloatUnaryOp
  | "abs" => some .abs | "neg" => some .neg | "sqrt" => some .sqrt
  | "ceil" => some .ceil | "floor" => some .floor | "trunc" => some .trunc
  | "nearest" => some .nearest | _ => none

private def vectorFloatBinary? : String → Option FloatBinaryOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "min" | "relaxed_min" => some .min | "max" | "relaxed_max" => some .max | _ => none

private def vectorFloatRel? : String → Option FloatRelOp
  | "eq" => some .eq | "ne" => some .ne | "lt" => some .lt
  | "gt" => some .gt | "le" => some .le | "ge" => some .ge | _ => none

/-- Vector floating arithmetic shares the scalar native arithmetic boundary. Relaxed fused
operations use the deterministic unfused profile. -/
def evalNativeVector (op : VectorOp) (args : List Value) : Option Value := do
  if !decide op.ImmediatesValid then return ← none
  let operation := (op.opcode.name.splitOn ".")[1]?.getD ""
  let width := op.opcode.laneWidth
  let float : NumWidth := if width == 64 then .w64 else .w32
  let lanes := List.range (128 / width)
  let make := fun values => Value.v128 (BitVec.ofNat 128 (vectorPack width values))
  let get := fun bits i => floatValue float (vectorLane width bits i)
  match args with
  | [.v128 a] =>
    if let some unary := vectorFloatUnary? operation then
      if !op.opcode.name.startsWith "f" then none else
        return make (← lanes.mapM fun i => do
          return (← evalUnary float unary (get a.toNat i)).unsigned)
    if operation.startsWith "trunc_sat" || operation.startsWith "relaxed_trunc" then
      let source : NumWidth := if (operation.splitOn "f64").length > 1 then .w64 else .w32
      let count := 128 / source.bits
      let signed := operation.endsWith "_s" || operation.endsWith "_s_zero"
      let values ← (List.range count).mapM fun i => do
        let some value ← evalConvert (.trunc .w32 source signed true)
          (floatValue source (vectorLane source.bits a.toNat i)) | none
        return value.unsigned
      return make (values ++ List.replicate (4 - count) 0)
    if operation.startsWith "convert_" then
      let signed := operation.endsWith "_s"
      return make (← lanes.mapM fun i => do
        let some value ← evalConvert (.convert float .w32 signed)
          (.i32 (BitVec.ofNat 32 (vectorLane 32 a.toNat i))) | none
        return value.unsigned)
    if operation == "demote_f64x2_zero" then
      let values ← (List.range 2).mapM fun i => do
        let some value ← evalConvert .demote
          (.f64 (BitVec.ofNat 64 (vectorLane 64 a.toNat i))) | none
        return value.unsigned
      return make (values ++ [0, 0])
    if operation == "promote_low_f32x4" then
      return make (← lanes.mapM fun i => do
        let some value ← evalConvert .promote
          (.f32 (BitVec.ofNat 32 (vectorLane 32 a.toNat i))) | none
        return value.unsigned)
    none
  | [.v128 a, .v128 b] =>
    if !op.opcode.name.startsWith "f" then none else do
      if let some binary := vectorFloatBinary? operation then
        return make (← lanes.mapM fun i => do
          return (← evalBinary float binary (get a.toNat i) (get b.toNat i)).unsigned)
      if let some relation := vectorFloatRel? operation then
        return make (← lanes.mapM fun i => do
          let value ← evalRel float relation (get a.toNat i) (get b.toNat i)
          return if value.unsigned == 0 then 0 else 2 ^ width - 1)
      if operation == "pmin" || operation == "pmax" then
        return make (← lanes.mapM fun i => do
          let x := get a.toNat i
          let y := get b.toNat i
          let comparison ← evalRel float .lt (if operation == "pmin" then y else x)
            (if operation == "pmin" then x else y)
          return (if comparison.unsigned != 0 then y else x).unsigned)
      none
  | [.v128 a, .v128 b, .v128 c] =>
    if operation != "relaxed_madd" && operation != "relaxed_nmadd" then none else
      return make (← lanes.mapM fun i => do
        let product ← evalBinary float .mul (get a.toNat i) (get b.toNat i)
        let product ← if operation == "relaxed_nmadd" then evalUnary float .neg product
          else some product
        return (← evalBinary float .add product (get c.toNat i)).unsigned)
  | _ => none

end Wasm.Native
