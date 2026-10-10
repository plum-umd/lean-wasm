import Wasm.FloatBits
import Init.Data.Float32

/-! Executable scalar floats. Native arithmetic has no execution soundness theorem.
NaN-producing arithmetic chooses a canonical NaN allowed by Wasm's result sets.
https://webassembly.github.io/spec/core/exec/numerics.html -/
namespace Wasm.Native

private def canonicalize (width : NumWidth) (bits : Nat) : Nat :=
  if floatIsNaN width bits then width.canonicalNaN else bits

private def nativeUnary32 (op : FloatUnaryOp) (x : Float32) : Float32 :=
  match op with
  | .ceil => x.ceil | .floor => x.floor | .sqrt => x.sqrt
  | _ => x

private def nativeUnary64 (op : FloatUnaryOp) (x : Float) : Float :=
  match op with
  | .ceil => x.ceil | .floor => x.floor | .sqrt => x.sqrt
  | _ => x

private def roundIntegral (width : NumWidth) (bits : Nat) (nearest : Bool) : Nat := Id.run do
  let magnitude := bits % width.signBit
  let field := magnitude / 2 ^ width.fractionBits
  if field ≥ width.bias + width.fractionBits then return bits
  let integer := (truncateFloatBits width bits).natAbs
  let truncated := roundFloatRatio width integer 1
  if !nearest then return bits / width.signBit * width.signBit + truncated
  -- Distances and tie parity are exact in binary64 for both represented formats.
  let x := match width with
    | .w32 => (Float32.ofBits (UInt32.ofNat magnitude)).toFloat
    | .w64 => Float.ofBits (UInt64.ofNat magnitude)
  let delta := x - (UInt64.ofNat integer).toFloat
  let increment := delta > 0.5 || (delta == 0.5 && integer % 2 == 1)
  bits / width.signBit * width.signBit +
    roundFloatRatio width (integer + if increment then 1 else 0) 1

def evalUnary (width : NumWidth) (op : FloatUnaryOp) (value : Value) : Option Value := do
  let bits ← floatBits? width value
  let result := match op with
    | .abs => bits % width.signBit
    | .neg => (bits + width.signBit) % (2 * width.signBit)
    | .trunc | .nearest =>
      if floatIsNaN width bits then width.canonicalNaN
      else roundIntegral width bits (op == .nearest)
    | _ => canonicalize width (match width with
      | .w32 => (nativeUnary32 op (Float32.ofBits (UInt32.ofNat bits))).toBits.toNat
      | .w64 => (nativeUnary64 op (Float.ofBits (UInt64.ofNat bits))).toBits.toNat)
  return floatValue width result

private def nativeBinary32 (op : FloatBinaryOp) (a b : Float32) : Float32 :=
  match op with
  | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b
  | _ => a

private def nativeBinary64 (op : FloatBinaryOp) (a b : Float) : Float :=
  match op with
  | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b
  | _ => a

private def asFloat (width : NumWidth) (bits : Nat) : Float :=
  match width with
  | .w32 => (Float32.ofBits (UInt32.ofNat bits)).toFloat
  | .w64 => Float.ofBits (UInt64.ofNat bits)

def evalBinary (width : NumWidth) (op : FloatBinaryOp) (a b : Value) : Option Value := do
  let x ← floatBits? width a
  let y ← floatBits? width b
  let result := match op with
    | .copysign => x % width.signBit + y / width.signBit * width.signBit
    | .min | .max =>
      if floatIsNaN width x || floatIsNaN width y then width.canonicalNaN
      else if x % width.signBit == 0 && y % width.signBit == 0 then
        if op == .min then max x y else min x y
      else if asFloat width x < asFloat width y then
        if op == .min then x else y
      else if op == .min then y else x
    | _ => canonicalize width (match width with
      | .w32 => (nativeBinary32 op (Float32.ofBits (UInt32.ofNat x))
          (Float32.ofBits (UInt32.ofNat y))).toBits.toNat
      | .w64 => (nativeBinary64 op (Float.ofBits (UInt64.ofNat x))
          (Float.ofBits (UInt64.ofNat y))).toBits.toNat)
  return floatValue width result

def evalRel (width : NumWidth) (op : FloatRelOp) (a b : Value) : Option Value := do
  let x := asFloat width (← floatBits? width a)
  let y := asFloat width (← floatBits? width b)
  let result := match op with
    | .eq => x == y | .ne => !(x == y)
    | .lt => x < y | .gt => x > y | .le => x ≤ y | .ge => x ≥ y
  return .i32 (if result then 1 else 0)

private def intValue (width : NumWidth) (n : Int) : Value :=
  match width with
  | .w32 => .i32 (BitVec.ofInt 32 n) | .w64 => .i64 (BitVec.ofInt 64 n)

private def intBits? (width : NumWidth) (signed : Bool) : Value → Option Int
  | .i32 bits => if width = .w32 then some (if signed then bits.toInt else bits.toNat) else none
  | .i64 bits => if width = .w64 then some (if signed then bits.toInt else bits.toNat) else none
  | _ => none

/-- Outer `none` is a type mismatch; inner `none` is a Wasm conversion trap. -/
def evalConvert (op : FloatConversion) (value : Value) : Option (Option Value) := do
  match op with
  | .trunc integer float signed saturating =>
    let bits ← floatBits? float value
    let lower : Int := if signed then -(2 ^ (integer.bits - 1) : Int) else 0
    let upper : Int := if signed then 2 ^ (integer.bits - 1) - 1 else 2 ^ integer.bits - 1
    let nan := floatIsNaN float bits
    let infinity := bits % float.signBit == float.infinity
    let n := truncateFloatBits float bits
    if saturating then
      let clamped := if nan then 0 else if infinity then
        if bits ≥ float.signBit then lower else upper
        else max lower (min upper n)
      return some (intValue integer clamped)
    if nan || infinity || n < lower || n > upper then return none
    return some (intValue integer n)
  | .convert float integer signed =>
    let n ← intBits? integer signed value
    let bits := roundFloatRatio float n.natAbs 1
    return some (floatValue float (bits + if n < 0 then float.signBit else 0))
  | .demote =>
    let bits ← floatBits? .w64 value
    return some (floatValue .w32 (canonicalize .w32
      (Float.ofBits (UInt64.ofNat bits)).toFloat32.toBits.toNat))
  | .promote =>
    let bits ← floatBits? .w32 value
    return some (floatValue .w64 (canonicalize .w64
      (Float32.ofBits (UInt32.ofNat bits)).toFloat.toBits.toNat))
  | .reinterpretI32 =>
    let .f32 bits := value | none
    return some (.i32 bits)
  | .reinterpretI64 =>
    let .f64 bits := value | none
    return some (.i64 bits)
  | .reinterpretF32 =>
    let .i32 bits := value | none
    return some (.f32 bits)
  | .reinterpretF64 =>
    let .i64 bits := value | none
    return some (.f64 bits)

end Wasm.Native
