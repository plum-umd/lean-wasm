import Wasm.Module

namespace Wasm.Binary

inductive DecodeError where
  | malformed (offset : Nat) (message : String)
  | unsupported (offset : Nat) (message : String)
  deriving BEq, Repr

structure Reader where
  bytes : ByteArray
  offset : Nat := 0
  limit : Nat
  usesData : Bool := false

abbrev DecodeM := StateT Reader (Except DecodeError)

def malformed (message : String) : DecodeM α := do
  throw (.malformed (← get).offset message)

def unsupported (message : String) : DecodeM α := do
  throw (.unsupported (← get).offset message)

def byte : DecodeM Nat := do
  let reader ← get
  if reader.offset ≥ reader.limit then malformed "unexpected end of binary" else
    let some b := reader.bytes[reader.offset]? | malformed "unexpected end of binary"
    set {reader with offset := reader.offset + 1}
    return b.toNat

def peek : DecodeM Nat := do
  let reader ← get
  if reader.offset ≥ reader.limit then malformed "unexpected end of binary" else
    let some b := reader.bytes[reader.offset]? | malformed "unexpected end of binary"
    return b.toNat

def expect (value : Nat) : DecodeM Unit := do
  if (← byte) != value then malformed s!"expected byte {value}"

private def leb (signed : Bool) (width : Nat) : Nat → Nat → Nat → DecodeM Int
  | 0, _, _ => malformed "integer representation too long"
  | fuel + 1, shift, acc => do
    let b ← byte
    let value := acc + (b % 128) * 2^shift
    if b ≥ 128 then leb signed width fuel (shift + 7) value else
      let value : Int := if signed && b % 128 ≥ 64 then
        Int.ofNat value - Int.ofNat (2^(shift + 7)) else Int.ofNat value
      if signed then
        if value < -(Int.ofNat (2^(width - 1))) || value ≥ Int.ofNat (2^(width - 1)) then
          malformed "integer too large"
        else return value
      else if value ≥ Int.ofNat (2^width) then malformed "integer too large"
      else return value

def unsigned (width : Nat := 32) : DecodeM Nat :=
  (leb false width ((width + 6) / 7) 0 0).map Int.toNat

def signed (width : Nat) : DecodeM Int := leb true width ((width + 6) / 7) 0 0

def bytes (count : Nat) : DecodeM ByteArray := do
  let reader ← get
  if count > reader.limit - reader.offset then malformed "byte string extends past its boundary"
  let result := reader.bytes.extract reader.offset (reader.offset + count)
  set {reader with offset := reader.offset + count}
  return result

def blob : DecodeM ByteArray := do bytes (← unsigned)

def name : DecodeM String := do
  let raw ← blob
  let some text := String.fromUTF8? raw | malformed "name is not UTF-8"
  return text

def vector (item : DecodeM α) : DecodeM (List α) := do
  let n ← unsigned
  let reader ← get
  if n > reader.limit - reader.offset then malformed "truncated vector"
  let mut result := []
  for _ in [:n] do result := (← item) :: result
  return result.reverse

/-- Nested sections and function bodies cannot read past their declared length. -/
def sized (action : DecodeM α) : DecodeM α := do
  let length ← unsigned
  let reader ← get
  if length > reader.limit - reader.offset then malformed "declared size exceeds binary boundary"
  let boundary := reader.offset + length
  set {reader with limit := boundary}
  let result ← action
  let final ← get
  if final.offset != boundary then malformed "declared size does not match contents"
  set {final with limit := reader.limit}
  return result

def littleEndian (count : Nat) : DecodeM Nat := do
  let mut value := 0
  for i in [:count] do value := value + (← byte) * 2^(8*i)
  return value

end Wasm.Binary
