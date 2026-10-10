import Wasm.Syntax

/-! https://webassembly.github.io/spec/core/exec/numerics.html#integer-operations -/

namespace Wasm

/-- Bit-vector arithmetic implements reduction modulo 2^N, including subtraction. -/
def evalIntBinOp (op : IntBinOp) (a b : BitVec n) : BitVec n :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

/-- Natural-number presentation of the specification's modular integer operations. -/
def intBinOpSpec (op : IntBinOp) (n a b : Nat) : Nat :=
  match op with
  | .add => (a + b) % 2 ^ n
  | .sub => (a + 2 ^ n - b) % 2 ^ n
  | .mul => (a * b) % 2 ^ n

theorem evalIntBinOp_spec (op : IntBinOp) (a b : BitVec n) :
    (evalIntBinOp op a b).toNat = intBinOpSpec op n a.toNat b.toNat := by
  cases op
  · rfl
  · simp only [evalIntBinOp, intBinOpSpec, BitVec.toNat_sub]
    congr 1
    have hb := b.isLt
    omega
  · rfl

def evalBinOp : ValType → IntBinOp → Value → Value → Option Value
  | .i32, op, .i32 a, .i32 b => some (.i32 (evalIntBinOp op a b))
  | .i64, op, .i64 a, .i64 b => some (.i64 (evalIntBinOp op a b))
  | _, _, _, _ => none

/-- Both integer widths produce an i32 boolean for eqz. -/
def evalEqz : ValType → Value → Option Value
  | .i32, .i32 a => some (.i32 (if a = 0 then 1 else 0))
  | .i64, .i64 a => some (.i32 (if a = 0 then 1 else 0))
  | _, _ => none

end Wasm
