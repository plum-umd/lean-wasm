import Wasm.Numerics

/-!
Remaining scalar integer operations of WebAssembly 3.0.
https://webassembly.github.io/spec/core/exec/numerics.html#integer-operations
Floating-point conversions require floating-point values and are outside this module.
-/

namespace Wasm

def evalIntUnary (op : IntUnaryOp) (a : BitVec n) : BitVec n :=
  match op with
  | .clz => a.clz
  | .ctz => a.ctz
  | .popcnt => BitVec.ofNat n ((List.range n).countP fun i => a.getLsbD i)

/-- Undefined arithmetic primitives become traps at the instruction layer. -/
def evalIntBinary (op : IntBinaryOp) (a b : BitVec n) : Option (BitVec n) :=
  let shift := b.toNat % n
  match op with
  | .divU => if b = 0 then none else some (a.udiv b)
  | .divS =>
      if b = 0 ∨ (a.toInt = -(2 ^ (n - 1) : Int) ∧ b.toInt = -1) then none
      else some (BitVec.ofInt n (a.toInt.tdiv b.toInt))
  | .remU => if b = 0 then none else some (BitVec.ofNat n (a.toNat % b.toNat))
  | .remS => if b = 0 then none else some (BitVec.ofInt n (a.toInt.tmod b.toInt))
  | .and_ => some (a &&& b)
  | .or_ => some (a ||| b)
  | .xor => some (a ^^^ b)
  | .shl => some (a <<< shift)
  | .shrU => some (a >>> shift)
  | .shrS => some (a.sshiftRight shift)
  | .rotl => some (a.rotateLeft shift)
  | .rotr => some (a.rotateRight shift)

/-- Comparison results always become i32 booleans, regardless of operand width. -/
def evalIntRel (op : IntRelOp) (a b : BitVec n) : Bool :=
  match op with
  | .eq => a == b
  | .ne => a != b
  | .ltS => decide (a.toInt < b.toInt)
  | .ltU => decide (a.toNat < b.toNat)
  | .gtS => decide (a.toInt > b.toInt)
  | .gtU => decide (a.toNat > b.toNat)
  | .leS => decide (a.toInt ≤ b.toInt)
  | .leU => decide (a.toNat ≤ b.toNat)
  | .geS => decide (a.toInt ≥ b.toInt)
  | .geU => decide (a.toNat ≥ b.toNat)

inductive NumericResult where
  | value (result : Value)
  | trap
  deriving DecidableEq, Repr

def NumericResult.code : NumericResult → List AdminInstr
  | .value v => values [v]
  | .trap => [.trap]

private def liftPartial (pack : BitVec n → Value) : Option (BitVec n) → NumericResult
  | some v => .value (pack v)
  | none => .trap

def evalUnary : ValType → IntUnaryOp → Value → Option Value
  | .i32, op, .i32 a => some (.i32 (evalIntUnary op a))
  | .i64, op, .i64 a => some (.i64 (evalIntUnary op a))
  | _, _, _ => none

/-- `none` is a type mismatch; `some .trap` is a Wasm arithmetic trap. -/
def evalBinary : ValType → IntBinaryOp → Value → Value → Option NumericResult
  | .i32, op, .i32 a, .i32 b => some (liftPartial .i32 (evalIntBinary op a b))
  | .i64, op, .i64 a, .i64 b => some (liftPartial .i64 (evalIntBinary op a b))
  | _, _, _, _ => none

def evalRel : ValType → IntRelOp → Value → Value → Option Value
  | .i32, op, .i32 a, .i32 b => some (.i32 (if evalIntRel op a b then 1 else 0))
  | .i64, op, .i64 a, .i64 b => some (.i32 (if evalIntRel op a b then 1 else 0))
  | _, _, _, _ => none

def evalConversion : IntConversion → Value → Option Value
  | .wrapI64, .i64 a => some (.i32 (a.setWidth 32))
  | .extendI32S, .i32 a => some (.i64 (a.signExtend 64))
  | .extendI32U, .i32 a => some (.i64 (a.setWidth 64))
  | .extendI32_8S, .i32 a => some (.i32 ((a.setWidth 8).signExtend 32))
  | .extendI32_16S, .i32 a => some (.i32 ((a.setWidth 16).signExtend 32))
  | .extendI64_8S, .i64 a => some (.i64 ((a.setWidth 8).signExtend 64))
  | .extendI64_16S, .i64 a => some (.i64 ((a.setWidth 16).signExtend 64))
  | .extendI64_32S, .i64 a => some (.i64 ((a.setWidth 32).signExtend 64))
  | _, _ => none

theorem divS_undefined_iff (a b : BitVec n) :
    evalIntBinary .divS a b = none ↔
      b = 0 ∨ (a.toInt = -(2 ^ (n - 1) : Int) ∧ b.toInt = -1) := by
  simp only [evalIntBinary]
  split <;> simp_all

theorem remS_defined_iff (a b : BitVec n) :
    (∃ result, evalIntBinary .remS a b = some result) ↔ b ≠ 0 := by
  simp [evalIntBinary]

theorem divS_spec (a b : BitVec n) (hzero : b ≠ 0)
    (hoverflow : ¬(a.toInt = -(2 ^ (n - 1) : Int) ∧ b.toInt = -1)) :
    evalIntBinary .divS a b = some (BitVec.ofInt n (a.toInt.tdiv b.toInt)) := by
  change (if b = 0 ∨ _ then none else some _) = some _
  rw [if_neg (not_or_intro hzero hoverflow)]

theorem remS_spec (a b : BitVec n) (hzero : b ≠ 0) :
    evalIntBinary .remS a b = some (BitVec.ofInt n (a.toInt.tmod b.toInt)) := by
  change (if b = 0 then none else some _) = some _
  rw [if_neg hzero]

theorem evalUnary_type (h : evalUnary t op a = some v) : v.type = t := by
  cases t <;> cases a <;> simp [evalUnary] at h <;> cases h <;> rfl

theorem evalRel_type (h : evalRel t op a b = some v) : v.type = .i32 := by
  cases t <;> cases a <;> cases b <;> simp [evalRel] at h <;> cases h <;> rfl

theorem evalConversion_type (h : evalConversion op a = some v) : v.type = op.outputType := by
  cases op <;> cases a <;> simp [evalConversion] at h <;> cases h <;> rfl

end Wasm
