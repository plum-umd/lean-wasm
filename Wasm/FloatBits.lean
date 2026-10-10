import Wasm.Syntax

namespace Wasm

/-- IEEE encodings are stored as bits; this module performs no host float arithmetic. -/
def NumWidth.bits : NumWidth → Nat
  | .w32 => 32 | .w64 => 64

def NumWidth.fractionBits : NumWidth → Nat
  | .w32 => 23 | .w64 => 52

def NumWidth.bias : NumWidth → Nat
  | .w32 => 127 | .w64 => 1023

def NumWidth.signBit (width : NumWidth) : Nat := 2 ^ (width.bits - 1)
def NumWidth.infinity (width : NumWidth) : Nat := (2 * width.bias + 1) * 2 ^ width.fractionBits
def NumWidth.canonicalNaN (width : NumWidth) : Nat :=
  width.infinity + 2 ^ (width.fractionBits - 1)

def floatValue (width : NumWidth) (bits : Nat) : Value :=
  match width with
  | .w32 => .f32 (BitVec.ofNat 32 bits)
  | .w64 => .f64 (BitVec.ofNat 64 bits)

def floatBits? (width : NumWidth) : Value → Option Nat
  | .f32 bits => if width = .w32 then some bits.toNat else none
  | .f64 bits => if width = .w64 then some bits.toNat else none
  | _ => none

def floatIsNaN (width : NumWidth) (bits : Nat) : Bool :=
  bits % width.signBit > width.infinity

def floatIsCanonicalNaN (width : NumWidth) (bits : Nat) : Bool :=
  bits % width.signBit == width.canonicalNaN

def floatIsArithmeticNaN (width : NumWidth) (bits : Nat) : Bool :=
  floatIsNaN width bits && bits / 2 ^ (width.fractionBits - 1) % 2 == 1

private def scaledRatio (n d : Nat) (exponent : Int) : Nat × Nat :=
  if exponent ≥ 0 then (n * 2 ^ exponent.toNat, d)
  else (n, d * 2 ^ (-exponent).toNat)

private def roundedQuotient (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q

/-- Round an exact nonnegative rational once, to nearest with ties to even.
Correctness against the mathematical IEEE specification is not yet proved. -/
def roundFloatRatio (width : NumWidth) (n d : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let estimate : Int := (n.log2 : Int) - (d.log2 : Int)
  let (a, b) := scaledRatio d n estimate
  let exponent := if a > b then estimate - 1 else estimate
  let minimum : Int := 1 - (width.bias : Int)
  if exponent > (width.bias : Int) then return width.infinity
  let unit := max exponent minimum - (width.fractionBits : Int)
  let (a, b) := scaledRatio n d (-unit)
  let significand := roundedQuotient a b
  if exponent < minimum then return significand
  return min width.infinity
    ((exponent + (width.bias : Int)).toNat * 2 ^ width.fractionBits +
      (significand - 2 ^ width.fractionBits))

/-- Exact integer part of a finite IEEE encoding, truncating toward zero. -/
def truncateFloatBits (width : NumWidth) (bits : Nat) : Int :=
  let magnitude := bits % width.signBit
  let field := magnitude / 2 ^ width.fractionBits
  let fraction := magnitude % 2 ^ width.fractionBits
  let significand := if field == 0 then fraction else 2 ^ width.fractionBits + fraction
  let exponent : Int := (max field 1 : Int) - (width.bias : Int) - width.fractionBits
  let (n, d) := scaledRatio significand 1 exponent
  let integer := (n / d : Nat)
  if bits ≥ width.signBit then -(integer : Int) else (integer : Int)

end Wasm
