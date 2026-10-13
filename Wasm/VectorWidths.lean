import Wasm.VectorProofs
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
namespace Wasm.VectorProofs
private theorem nat_8 : "8".toNat? = some 8 := by
  have chars : "8".toSlice.chars.toList = ['8'] := by
    simp only [String.Slice.chars]
    rw [Std.Iterators.Iter.toList_map]
    simp only [String.Slice.positions]
    rw [Std.Iterators.Iter.toList_eq_match_step]
    simp +decide [Std.Iterators.Iter.step, Std.Iterators.IterM.step,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure,
      Std.Iterators.Iter.toIterM, Std.Iterators.Iter.toList_eq_match_step]
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, String.Slice.foldl,
    ← Std.Iterators.Iter.foldl_toList, chars]
  decide +kernel

private theorem nat_16 : "16".toNat? = some 16 := by
  have chars : "16".toSlice.chars.toList = ['1','6'] := by
    simp only [String.Slice.chars]
    rw [Std.Iterators.Iter.toList_map]
    simp only [String.Slice.positions]
    rw [Std.Iterators.Iter.toList_eq_match_step]
    simp +decide [Std.Iterators.Iter.step, Std.Iterators.IterM.step,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure,
      Std.Iterators.Iter.toIterM, Std.Iterators.Iter.toList_eq_match_step]
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, String.Slice.foldl,
    ← Std.Iterators.Iter.foldl_toList, chars]
  decide +kernel

private theorem nat_32 : "32".toNat? = some 32 := by
  have chars : "32".toSlice.chars.toList = ['3','2'] := by
    simp only [String.Slice.chars]
    rw [Std.Iterators.Iter.toList_map]
    simp only [String.Slice.positions]
    rw [Std.Iterators.Iter.toList_eq_match_step]
    simp +decide [Std.Iterators.Iter.step, Std.Iterators.IterM.step,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure,
      Std.Iterators.Iter.toIterM, Std.Iterators.Iter.toList_eq_match_step]
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, String.Slice.foldl,
    ← Std.Iterators.Iter.foldl_toList, chars]
  decide +kernel

private theorem nat_64 : "64".toNat? = some 64 := by
  have chars : "64".toSlice.chars.toList = ['6','4'] := by
    simp only [String.Slice.chars]
    rw [Std.Iterators.Iter.toList_map]
    simp only [String.Slice.positions]
    rw [Std.Iterators.Iter.toList_eq_match_step]
    simp +decide [Std.Iterators.Iter.step, Std.Iterators.IterM.step,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure,
      Std.Iterators.Iter.toIterM, Std.Iterators.Iter.toList_eq_match_step]
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, String.Slice.foldl,
    ← Std.Iterators.Iter.foldl_toList, chars]
  decide +kernel

private theorem nat_128 : "128".toNat? = some 128 := by
  have chars : "128".toSlice.chars.toList = ['1','2','8'] := by
    simp only [String.Slice.chars]
    rw [Std.Iterators.Iter.toList_map]
    simp only [String.Slice.positions]
    rw [Std.Iterators.Iter.toList_eq_match_step]
    simp +decide [Std.Iterators.Iter.step, Std.Iterators.IterM.step,
      String.Slice.PosIterator.instIteratorSubtypePosNeEndPosOfPure,
      Std.Iterators.Iter.toIterM, Std.Iterators.Iter.toList_eq_match_step]
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat, String.Slice.foldl,
    ← Std.Iterators.Iter.foldl_toList, chars]
  decide +kernel


private theorem ofList_8 : String.ofList ['8'] = "8" := by decide +kernel
private theorem ofList_16 : String.ofList ['1','6'] = "16" := by decide +kernel
private theorem ofList_32 : String.ofList ['3','2'] = "32" := by decide +kernel
private theorem ofList_64 : String.ofList ['6','4'] = "64" := by decide +kernel
private theorem ofList_128 : String.ofList ['1','2','8'] = "128" := by decide +kernel
noncomputable def laneWidth : VectorOpcode → Nat
  | .v128_load => 128
  | .v128_load8x8_s => 128
  | .v128_load8x8_u => 128
  | .v128_load16x4_s => 128
  | .v128_load16x4_u => 128
  | .v128_load32x2_s => 128
  | .v128_load32x2_u => 128
  | .v128_load8_splat => 128
  | .v128_load16_splat => 128
  | .v128_load32_splat => 128
  | .v128_load64_splat => 128
  | .v128_store => 128
  | .v128_const => 128
  | .i8x16_shuffle => 8
  | .i8x16_swizzle => 8
  | .i8x16_splat => 8
  | .i16x8_splat => 16
  | .i32x4_splat => 32
  | .i64x2_splat => 64
  | .f32x4_splat => 32
  | .f64x2_splat => 64
  | .i8x16_extract_lane_s => 8
  | .i8x16_extract_lane_u => 8
  | .i8x16_replace_lane => 8
  | .i16x8_extract_lane_s => 16
  | .i16x8_extract_lane_u => 16
  | .i16x8_replace_lane => 16
  | .i32x4_extract_lane => 32
  | .i32x4_replace_lane => 32
  | .i64x2_extract_lane => 64
  | .i64x2_replace_lane => 64
  | .f32x4_extract_lane => 32
  | .f32x4_replace_lane => 32
  | .f64x2_extract_lane => 64
  | .f64x2_replace_lane => 64
  | .i8x16_eq => 8
  | .i8x16_ne => 8
  | .i8x16_lt_s => 8
  | .i8x16_lt_u => 8
  | .i8x16_gt_s => 8
  | .i8x16_gt_u => 8
  | .i8x16_le_s => 8
  | .i8x16_le_u => 8
  | .i8x16_ge_s => 8
  | .i8x16_ge_u => 8
  | .i16x8_eq => 16
  | .i16x8_ne => 16
  | .i16x8_lt_s => 16
  | .i16x8_lt_u => 16
  | .i16x8_gt_s => 16
  | .i16x8_gt_u => 16
  | .i16x8_le_s => 16
  | .i16x8_le_u => 16
  | .i16x8_ge_s => 16
  | .i16x8_ge_u => 16
  | .i32x4_eq => 32
  | .i32x4_ne => 32
  | .i32x4_lt_s => 32
  | .i32x4_lt_u => 32
  | .i32x4_gt_s => 32
  | .i32x4_gt_u => 32
  | .i32x4_le_s => 32
  | .i32x4_le_u => 32
  | .i32x4_ge_s => 32
  | .i32x4_ge_u => 32
  | .f32x4_eq => 32
  | .f32x4_ne => 32
  | .f32x4_lt => 32
  | .f32x4_gt => 32
  | .f32x4_le => 32
  | .f32x4_ge => 32
  | .f64x2_eq => 64
  | .f64x2_ne => 64
  | .f64x2_lt => 64
  | .f64x2_gt => 64
  | .f64x2_le => 64
  | .f64x2_ge => 64
  | .v128_not => 128
  | .v128_and => 128
  | .v128_andnot => 128
  | .v128_or => 128
  | .v128_xor => 128
  | .v128_bitselect => 128
  | .v128_any_true => 128
  | .v128_load8_lane => 128
  | .v128_load16_lane => 128
  | .v128_load32_lane => 128
  | .v128_load64_lane => 128
  | .v128_store8_lane => 128
  | .v128_store16_lane => 128
  | .v128_store32_lane => 128
  | .v128_store64_lane => 128
  | .v128_load32_zero => 128
  | .v128_load64_zero => 128
  | .f32x4_demote_f64x2_zero => 32
  | .f64x2_promote_low_f32x4 => 64
  | .i8x16_abs => 8
  | .i8x16_neg => 8
  | .i8x16_popcnt => 8
  | .i8x16_all_true => 8
  | .i8x16_bitmask => 8
  | .i8x16_narrow_i16x8_s => 8
  | .i8x16_narrow_i16x8_u => 8
  | .f32x4_ceil => 32
  | .f32x4_floor => 32
  | .f32x4_trunc => 32
  | .f32x4_nearest => 32
  | .i8x16_shl => 8
  | .i8x16_shr_s => 8
  | .i8x16_shr_u => 8
  | .i8x16_add => 8
  | .i8x16_add_sat_s => 8
  | .i8x16_add_sat_u => 8
  | .i8x16_sub => 8
  | .i8x16_sub_sat_s => 8
  | .i8x16_sub_sat_u => 8
  | .f64x2_ceil => 64
  | .f64x2_floor => 64
  | .i8x16_min_s => 8
  | .i8x16_min_u => 8
  | .i8x16_max_s => 8
  | .i8x16_max_u => 8
  | .f64x2_trunc => 64
  | .i8x16_avgr_u => 8
  | .i16x8_extadd_pairwise_i8x16_s => 16
  | .i16x8_extadd_pairwise_i8x16_u => 16
  | .i32x4_extadd_pairwise_i16x8_s => 32
  | .i32x4_extadd_pairwise_i16x8_u => 32
  | .i16x8_abs => 16
  | .i16x8_neg => 16
  | .i16x8_q15mulr_sat_s => 16
  | .i16x8_all_true => 16
  | .i16x8_bitmask => 16
  | .i16x8_narrow_i32x4_s => 16
  | .i16x8_narrow_i32x4_u => 16
  | .i16x8_extend_low_i8x16_s => 16
  | .i16x8_extend_high_i8x16_s => 16
  | .i16x8_extend_low_i8x16_u => 16
  | .i16x8_extend_high_i8x16_u => 16
  | .i16x8_shl => 16
  | .i16x8_shr_s => 16
  | .i16x8_shr_u => 16
  | .i16x8_add => 16
  | .i16x8_add_sat_s => 16
  | .i16x8_add_sat_u => 16
  | .i16x8_sub => 16
  | .i16x8_sub_sat_s => 16
  | .i16x8_sub_sat_u => 16
  | .f64x2_nearest => 64
  | .i16x8_mul => 16
  | .i16x8_min_s => 16
  | .i16x8_min_u => 16
  | .i16x8_max_s => 16
  | .i16x8_max_u => 16
  | .i16x8_avgr_u => 16
  | .i16x8_extmul_low_i8x16_s => 16
  | .i16x8_extmul_high_i8x16_s => 16
  | .i16x8_extmul_low_i8x16_u => 16
  | .i16x8_extmul_high_i8x16_u => 16
  | .i32x4_abs => 32
  | .i32x4_neg => 32
  | .i32x4_all_true => 32
  | .i32x4_bitmask => 32
  | .i32x4_extend_low_i16x8_s => 32
  | .i32x4_extend_high_i16x8_s => 32
  | .i32x4_extend_low_i16x8_u => 32
  | .i32x4_extend_high_i16x8_u => 32
  | .i32x4_shl => 32
  | .i32x4_shr_s => 32
  | .i32x4_shr_u => 32
  | .i32x4_add => 32
  | .i32x4_sub => 32
  | .i32x4_mul => 32
  | .i32x4_min_s => 32
  | .i32x4_min_u => 32
  | .i32x4_max_s => 32
  | .i32x4_max_u => 32
  | .i32x4_dot_i16x8_s => 32
  | .i32x4_extmul_low_i16x8_s => 32
  | .i32x4_extmul_high_i16x8_s => 32
  | .i32x4_extmul_low_i16x8_u => 32
  | .i32x4_extmul_high_i16x8_u => 32
  | .i64x2_abs => 64
  | .i64x2_neg => 64
  | .i64x2_all_true => 64
  | .i64x2_bitmask => 64
  | .i64x2_extend_low_i32x4_s => 64
  | .i64x2_extend_high_i32x4_s => 64
  | .i64x2_extend_low_i32x4_u => 64
  | .i64x2_extend_high_i32x4_u => 64
  | .i64x2_shl => 64
  | .i64x2_shr_s => 64
  | .i64x2_shr_u => 64
  | .i64x2_add => 64
  | .i64x2_sub => 64
  | .i64x2_mul => 64
  | .i64x2_eq => 64
  | .i64x2_ne => 64
  | .i64x2_lt_s => 64
  | .i64x2_gt_s => 64
  | .i64x2_le_s => 64
  | .i64x2_ge_s => 64
  | .i64x2_extmul_low_i32x4_s => 64
  | .i64x2_extmul_high_i32x4_s => 64
  | .i64x2_extmul_low_i32x4_u => 64
  | .i64x2_extmul_high_i32x4_u => 64
  | .f32x4_abs => 32
  | .f32x4_neg => 32
  | .f32x4_sqrt => 32
  | .f32x4_add => 32
  | .f32x4_sub => 32
  | .f32x4_mul => 32
  | .f32x4_div => 32
  | .f32x4_min => 32
  | .f32x4_max => 32
  | .f32x4_pmin => 32
  | .f32x4_pmax => 32
  | .f64x2_abs => 64
  | .f64x2_neg => 64
  | .f64x2_sqrt => 64
  | .f64x2_add => 64
  | .f64x2_sub => 64
  | .f64x2_mul => 64
  | .f64x2_div => 64
  | .f64x2_min => 64
  | .f64x2_max => 64
  | .f64x2_pmin => 64
  | .f64x2_pmax => 64
  | .i32x4_trunc_sat_f32x4_s => 32
  | .i32x4_trunc_sat_f32x4_u => 32
  | .f32x4_convert_i32x4_s => 32
  | .f32x4_convert_i32x4_u => 32
  | .i32x4_trunc_sat_f64x2_s_zero => 32
  | .i32x4_trunc_sat_f64x2_u_zero => 32
  | .f64x2_convert_low_i32x4_s => 64
  | .f64x2_convert_low_i32x4_u => 64
  | .i8x16_relaxed_swizzle => 8
  | .i32x4_relaxed_trunc_f32x4_s => 32
  | .i32x4_relaxed_trunc_f32x4_u => 32
  | .i32x4_relaxed_trunc_f64x2_s => 32
  | .i32x4_relaxed_trunc_f64x2_u => 32
  | .f32x4_relaxed_madd => 32
  | .f32x4_relaxed_nmadd => 32
  | .f64x2_relaxed_madd => 64
  | .f64x2_relaxed_nmadd => 64
  | .i8x16_relaxed_laneselect => 8
  | .i16x8_relaxed_laneselect => 16
  | .i32x4_relaxed_laneselect => 32
  | .i64x2_relaxed_laneselect => 64
  | .f32x4_relaxed_min => 32
  | .f32x4_relaxed_max => 32
  | .f64x2_relaxed_min => 64
  | .f64x2_relaxed_max => 64
  | .i16x8_relaxed_q15mulr_s => 16
  | .i16x8_relaxed_dot_i8x16_i7x16_s => 16
  | .i32x4_relaxed_dot_i8x16_i7x16_add_s => 32

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem laneWidth_eq (opcode : VectorOpcode) : opcode.laneWidth = laneWidth opcode := by
  cases opcode <;> simp only [VectorOpcode.laneWidth, name_split]
  all_goals dsimp only [nameParts, laneWidth,
    List.head!, List.headD, List.head?_cons, Option.getD_some]
  all_goals string_list_facts
  all_goals simp_all only [List.drop, List.takeWhile, Char.isDigit]
  all_goals simp_all +decide [Char.isDigit, ofList_8, ofList_16, ofList_32, ofList_64, ofList_128, nat_8, nat_16, nat_32, nat_64, nat_128]

#print axioms laneWidth_eq
end Wasm.VectorProofs
