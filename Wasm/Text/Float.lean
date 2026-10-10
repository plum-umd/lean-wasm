import Wasm.FloatBits

namespace Wasm.Text

private def floatDigits (base : Nat) (s : String) : Except String Nat := do
  if s.isEmpty then throw "missing float digits"
  let mut value := 0
  let mut previousDigit := false
  for c in s.toList do
    if c == '_' then
      if !previousDigit then throw "misplaced float separator"
      previousDigit := false
    else
      let d := if c.isDigit then c.toNat - 48
        else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
        else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55 else base
      if d ≥ base then throw "invalid float digit"
      value := value * base + d
      previousDigit := true
  if !previousDigit then throw "trailing float separator"
  return value

private def floatExponent (s : String) : Except String Int := do
  let (negative, rest) := if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString) else (false, s)
  let n ← floatDigits 10 rest
  return if negative then -(n : Int) else (n : Int)

/-- Parse decimal/hexadecimal literals through exact rationals, rounding once.
Literal parsing and numerical rounding have not yet been formally verified. -/
def floatLiteral (width : NumWidth) (literal : String) : Except String Value := do
  let (negative, s) := if literal.startsWith "-" then (true, (literal.drop 1).toString)
    else if literal.startsWith "+" then (false, (literal.drop 1).toString) else (false, literal)
  let sign := if negative then width.signBit else 0
  if s == "inf" then return floatValue width (sign + width.infinity)
  if s == "nan" then return floatValue width (sign + width.canonicalNaN)
  if s.startsWith "nan:0x" then
    let payload ← floatDigits 16 (s.drop 6).toString
    if payload == 0 || payload ≥ 2 ^ width.fractionBits then throw "NaN payload out of range"
    return floatValue width (sign + width.infinity + payload)
  let hex := s.startsWith "0x"
  let base := if hex then 16 else 10
  let body := if hex then (s.drop 2).toString else s
  let body := body.map fun c => if hex && c == 'P' then 'p'
    else if !hex && c == 'E' then 'e' else c
  let parts := body.splitOn (if hex then "p" else "e")
  let (mantissa, exponent) ← match parts with
    | [m] => pure (m, (0 : Int))
    | [m, e] => pure (m, ← floatExponent e)
    | _ => throw "float exponent syntax"
  let (whole, fraction) ← match mantissa.splitOn "." with
    | [whole] => pure (whole, "")
    | [whole, fraction] => pure (whole, fraction)
    | _ => throw "float significand syntax"
  let _ ← floatDigits base whole
  if !fraction.isEmpty then let _ ← floatDigits base fraction; pure ()
  let digits := (whole ++ fraction).replace "_" ""
  let numerator ← floatDigits base digits
  let fractionalDigits := (fraction.replace "_" "").length
  let exponent := exponent - (if hex then 4 else 1) * (fractionalDigits : Int)
  if numerator == 0 then return floatValue width sign
  -- Avoid enormous powers for literals whose exponent already determines their rounding.
  if exponent > 5000 then throw "float literal overflows"
  if exponent < -(5000 + (digits.length : Int) * 4) then return floatValue width sign
  let powerBase := if hex then 2 else 10
  let (n, d) := if exponent ≥ 0 then (numerator * powerBase ^ exponent.toNat, 1)
    else (numerator, powerBase ^ (-exponent).toNat)
  let bits := roundFloatRatio width n d
  if bits == width.infinity then throw "float literal overflows"
  return floatValue width (sign + bits)

end Wasm.Text
