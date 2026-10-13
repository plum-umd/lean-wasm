import Wasm.VectorStringFacts
import Wasm.VectorValidation

namespace Wasm

/-- Lane zero occupies the least significant bits, independently of host byte order. -/
def vectorLane (width : Nat) (bits : Nat) (lane : Nat) : Nat :=
  bits / 2 ^ (width * lane) % 2 ^ width

def vectorPack (width : Nat) (lanes : List Nat) : Nat :=
  lanes.foldr (fun lane rest => lane % 2 ^ width + 2 ^ width * rest) 0

def vectorSigned (width bits : Nat) : Int :=
  if bits < 2 ^ (width - 1) then bits else (bits : Int) - (2 ^ width : Nat)

def vectorWrap (width : Nat) (value : Int) : Nat :=
  (value % (2 ^ width : Nat)).toNat

def vectorSaturate (width : Nat) (signed : Bool) (value : Int) : Nat :=
  let lower : Int := if signed then -(2 ^ (width - 1) : Nat) else 0
  let upper : Int := if signed then (2 ^ (width - 1) : Nat) - 1 else (2 ^ width : Nat) - 1
  vectorWrap width (max lower (min upper value))


private def vectorValue (width : Nat) (lanes : List Nat) : Value :=
  .v128 (BitVec.ofNat 128 (vectorPack width lanes))

private def bits128? : Value → Option Nat
  | .v128 bits => some bits.toNat
  | _ => none

private def laneBinary (width : Nat) (operation : String) (a b : Nat) : Option Nat := do
  let sa := vectorSigned width a
  let sb := vectorSigned width b
  let signed := operation.endsWith "_s"
  let x : Int := if signed then sa else a
  let y : Int := if signed then sb else b
  let mask := 2 ^ width - 1
  match operation with
  | "add" => return (a + b) % 2 ^ width
  | "sub" => return vectorWrap width (sa - sb)
  | "mul" => return (a * b) % 2 ^ width
  | "add_sat_s" | "add_sat_u" => return vectorSaturate width signed (x + y)
  | "sub_sat_s" | "sub_sat_u" => return vectorSaturate width signed (x - y)
  | "min_s" | "min_u" => return vectorWrap width (min x y)
  | "max_s" | "max_u" => return vectorWrap width (max x y)
  | "avgr_u" => return (a + b + 1) / 2
  | "eq" => return if a == b then mask else 0
  | "ne" => return if a != b then mask else 0
  | "lt_s" | "lt_u" => return if x < y then mask else 0
  | "gt_s" | "gt_u" => return if x > y then mask else 0
  | "le_s" | "le_u" => return if x ≤ y then mask else 0
  | "ge_s" | "ge_u" => return if x ≥ y then mask else 0
  | "q15mulr_sat_s" | "relaxed_q15mulr_s" =>
    return vectorSaturate width true ((sa * sb + 16384) / 32768)
  | _ => none

/-- Integer and bitwise SIMD equations use arbitrary precision intermediates. Floating arithmetic
is handled separately by the native backend. -/
def evalVector (op : VectorOp) (args : List Value) : Option Value := do
  if !decide op.ImmediatesValid then return ← none
  let width := op.opcode.laneWidth
  let operation := (op.opcode.name.splitOn ".")[1]?.getD ""
  let lanes := List.range (128 / width)
  let lane := vectorLane width
  let packed := vectorValue width
  let immediate := op.lanes.headD 0
  match args with
  | [value] =>
    if operation == "splat" then
      if value.type != op.opcode.signature.params.headD .v128 then none
      else return packed (lanes.map fun _ => value.unsigned)
    else do
      let bits ← bits128? value
      if operation.startsWith "extract_lane" then
        let n := lane bits immediate
        return Value.ofInt (op.opcode.signature.results.headD .i32)
          (if operation.endsWith "_s" then vectorSigned width n else n)
      if op.opcode == .v128_not then
        return .v128 (BitVec.ofNat 128 (Nat.xor bits (2 ^ 128 - 1)))
      if op.opcode == .v128_any_true then
        return .i32 (if bits == 0 then 0 else 1)
      if operation == "all_true" then
        return .i32 (if lanes.all (fun i => lane bits i != 0) then 1 else 0)
      if operation == "bitmask" then
        return .i32 (BitVec.ofNat 32 ((lanes.map fun i =>
          lane bits i / 2 ^ (width - 1) * 2 ^ i).foldl (· + ·) 0))
      if op.opcode.name.startsWith "f" && (operation == "abs" || operation == "neg") then
        return packed (lanes.map fun i =>
          let n := lane bits i
          if operation == "abs" then n % 2 ^ (width - 1)
          else Nat.xor n (2 ^ (width - 1)))
      if operation == "abs" && op.opcode.name.startsWith "i" then
        return packed (lanes.map fun i => (vectorSigned width (lane bits i)).natAbs)
      if operation == "neg" && op.opcode.name.startsWith "i" then
        return packed (lanes.map fun i => vectorWrap width (-(vectorSigned width (lane bits i))))
      if operation == "popcnt" then
        return packed (lanes.map fun i => ((List.range width).filter
          (fun b => lane bits i / 2 ^ b % 2 == 1)).length)
      if operation.startsWith "extend_" then
        let source := width / 2
        let offset := if operation.startsWith "extend_high" then 128 / width else 0
        return packed (lanes.map fun i =>
          let n := vectorLane source bits (i + offset)
          if operation.endsWith "_s" then vectorWrap width (vectorSigned source n) else n)
      if operation.startsWith "extadd_pairwise" then
        let source := width / 2
        let get := fun i =>
          let n := vectorLane source bits i
          if operation.endsWith "_s" then vectorSigned source n else (n : Int)
        return packed (lanes.map fun i => vectorWrap width (get (2*i) + get (2*i+1)))
      none
  | [a, b] =>
    let x ← bits128? a
    if operation == "replace_lane" then
      if b.type != op.opcode.signature.params[1]?.getD .v128 then none else
        return packed (lanes.map fun i => if i == immediate then b.unsigned else lane x i)
    if operation == "shl" || operation == "shr_s" || operation == "shr_u" then
      let .i32 shift := b | none
      let shift := shift.toNat % width
      return packed (lanes.map fun i =>
        let n := lane x i
        if operation == "shl" then n * 2 ^ shift
        else if operation == "shr_s" then
          vectorWrap width (vectorSigned width n / (2 ^ shift : Nat))
        else n / 2 ^ shift)
    let y ← bits128? b
    if op.opcode == .v128_and then return .v128 (BitVec.ofNat 128 (Nat.land x y))
    if op.opcode == .v128_andnot then
      return .v128 (BitVec.ofNat 128 (Nat.land x (Nat.xor y (2 ^ 128 - 1))))
    if op.opcode == .v128_or then return .v128 (BitVec.ofNat 128 (Nat.lor x y))
    if op.opcode == .v128_xor then return .v128 (BitVec.ofNat 128 (Nat.xor x y))
    if operation == "shuffle" then
      return vectorValue 8 (op.lanes.map fun i => vectorLane 8 (if i < 16 then x else y) (i % 16))
    if operation == "swizzle" || operation == "relaxed_swizzle" then
      return packed (lanes.map fun i =>
        let index := lane y i
        if index < 16 then lane x index else 0)
    if operation.startsWith "narrow_" then
      let source := 2 * width
      let narrow := fun bits => (List.range (128 / source)).map fun i =>
        vectorSaturate width (operation.endsWith "_s")
          (vectorSigned source (vectorLane source bits i))
      return packed (narrow x ++ narrow y)
    if operation.startsWith "extmul_" then
      let source := width / 2
      let offset := if operation.startsWith "extmul_high" then 128 / width else 0
      let get := fun bits i =>
        let n := vectorLane source bits (i + offset)
        if operation.endsWith "_s" then vectorSigned source n else (n : Int)
      return packed (lanes.map fun i => vectorWrap width (get x i * get y i))
    if operation == "dot_i16x8_s" || operation == "relaxed_dot_i8x16_i7x16_s" then
      let source := width / 2
      let product := fun i => vectorSigned source (vectorLane source x i) *
        vectorSigned source (vectorLane source y i)
      return packed (lanes.map fun i => vectorWrap width (product (2*i) + product (2*i+1)))
    if op.opcode.name.startsWith "f" then none else
      return packed (← lanes.mapM fun i => laneBinary width operation (lane x i) (lane y i))
  | [a, b, c] =>
    let x ← bits128? a
    let y ← bits128? b
    let z ← bits128? c
    if operation == "bitselect" || operation == "relaxed_laneselect" then
      return .v128 (BitVec.ofNat 128
        (Nat.lor (Nat.land x z) (Nat.land y (Nat.xor z (2 ^ 128 - 1)))))
    if operation == "relaxed_dot_i8x16_i7x16_add_s" then
      let product := fun i => vectorSigned 8 (vectorLane 8 x i) *
        vectorSigned 8 (vectorLane 8 y i)
      return packed (lanes.map fun i => vectorWrap 32 ((vectorLane 32 z i : Int) +
        product (4*i) + product (4*i+1) + product (4*i+2) + product (4*i+3)))
    none
  | _ => none


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem evalVector_one_arity (found : evalVector op [argument] = some value) :
    op.opcode.signature.params.length = 1 ∧ op.opcode.isMemory = false := by
  cases op with
  | mk opcode arg lanes memory =>
    cases opcode <;>
      dsimp only [VectorOpcode.signature, VectorOpcode.isMemory, VectorOpcode.name,
        List.length_cons, List.length_nil]
    all_goals try decide +kernel
    all_goals simp only [evalVector, VectorProofs.laneWidth_eq] at found
    all_goals dsimp only [VectorProofs.laneWidth] at found
    all_goals simp only [VectorProofs.name_split] at found
    all_goals dsimp only [VectorProofs.nameParts] at found
    all_goals try dsimp only [VectorOpcode.name] at found
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.head!, List.headD] at found
    all_goals closed_string_tests
    all_goals simp only [*] at found
    all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, Bool.or_false,
      Bool.false_or, Bool.and_false, Bool.false_and, ite_false, ite_true] at found
    all_goals simp_all [bits128?]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem evalVector_two_arity (found : evalVector op [left, right] = some value) :
    op.opcode.signature.params.length = 2 ∧ op.opcode.isMemory = false := by
  cases op with
  | mk opcode arg lanes memory =>
    cases opcode <;>
      dsimp only [VectorOpcode.signature, VectorOpcode.isMemory, VectorOpcode.name,
        List.length_cons, List.length_nil]
    all_goals try decide +kernel
    all_goals simp only [evalVector, VectorProofs.laneWidth_eq] at found
    all_goals dsimp only [VectorProofs.laneWidth] at found
    all_goals simp only [VectorProofs.name_split] at found
    all_goals dsimp only [VectorProofs.nameParts] at found
    all_goals try dsimp only [VectorOpcode.name] at found
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.head!, List.headD] at found
    all_goals closed_string_tests
    all_goals simp only [*] at found
    all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, Bool.or_false,
      Bool.false_or, Bool.and_false, Bool.false_and, ite_false, ite_true] at found
    all_goals simp_all [bits128?, laneBinary, List.range, List.range.loop]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
private theorem evalVector_three_arity (found : evalVector op [left, middle, right] = some value) :
    op.opcode.signature.params.length = 3 ∧ op.opcode.isMemory = false := by
  cases op with
  | mk opcode arg lanes memory =>
    cases opcode <;>
      dsimp only [VectorOpcode.signature, VectorOpcode.isMemory, VectorOpcode.name,
        List.length_cons, List.length_nil]
    all_goals try decide +kernel
    all_goals simp only [evalVector, VectorProofs.laneWidth_eq] at found
    all_goals dsimp only [VectorProofs.laneWidth] at found
    all_goals simp only [VectorProofs.name_split] at found
    all_goals dsimp only [VectorProofs.nameParts] at found
    all_goals try dsimp only [VectorOpcode.name] at found
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.head!, List.headD] at found
    all_goals closed_string_tests
    all_goals simp only [*] at found
    all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, Bool.or_false,
      Bool.false_or, Bool.and_false, Bool.false_and, ite_false, ite_true] at found
    all_goals simp_all [bits128?]


/-- Successful SIMD evaluation uses the declared operand arity and a pure opcode. -/
theorem evalVector_arity (found : evalVector op args = some value) :
    args.length = op.opcode.signature.params.length ∧ op.opcode.isMemory = false := by
  cases args with
  | nil => simp [evalVector] at found
  | cons a rest =>
    cases rest with
    | nil =>
      obtain ⟨arity, memory⟩ := evalVector_one_arity found
      exact ⟨by simpa using arity.symm, memory⟩
    | cons b rest =>
      cases rest with
      | nil =>
        obtain ⟨arity, memory⟩ := evalVector_two_arity found
        exact ⟨by simpa using arity.symm, memory⟩
      | cons c rest =>
        cases rest with
        | nil =>
          obtain ⟨arity, memory⟩ := evalVector_three_arity found
          exact ⟨by simpa using arity.symm, memory⟩
        | cons d rest => simp [evalVector] at found

#print axioms evalVector_arity

#print axioms evalVector_one_arity
end Wasm
