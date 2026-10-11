import Std

namespace Wasm

/-- SIMD opcodes from the Wasm 3.0 instruction index (2026-10-09). -/
inductive VectorOpcode where
  | v128_load
  | v128_load8x8_s
  | v128_load8x8_u
  | v128_load16x4_s
  | v128_load16x4_u
  | v128_load32x2_s
  | v128_load32x2_u
  | v128_load8_splat
  | v128_load16_splat
  | v128_load32_splat
  | v128_load64_splat
  | v128_store
  | v128_const
  | i8x16_shuffle
  | i8x16_swizzle
  | i8x16_splat
  | i16x8_splat
  | i32x4_splat
  | i64x2_splat
  | f32x4_splat
  | f64x2_splat
  | i8x16_extract_lane_s
  | i8x16_extract_lane_u
  | i8x16_replace_lane
  | i16x8_extract_lane_s
  | i16x8_extract_lane_u
  | i16x8_replace_lane
  | i32x4_extract_lane
  | i32x4_replace_lane
  | i64x2_extract_lane
  | i64x2_replace_lane
  | f32x4_extract_lane
  | f32x4_replace_lane
  | f64x2_extract_lane
  | f64x2_replace_lane
  | i8x16_eq
  | i8x16_ne
  | i8x16_lt_s
  | i8x16_lt_u
  | i8x16_gt_s
  | i8x16_gt_u
  | i8x16_le_s
  | i8x16_le_u
  | i8x16_ge_s
  | i8x16_ge_u
  | i16x8_eq
  | i16x8_ne
  | i16x8_lt_s
  | i16x8_lt_u
  | i16x8_gt_s
  | i16x8_gt_u
  | i16x8_le_s
  | i16x8_le_u
  | i16x8_ge_s
  | i16x8_ge_u
  | i32x4_eq
  | i32x4_ne
  | i32x4_lt_s
  | i32x4_lt_u
  | i32x4_gt_s
  | i32x4_gt_u
  | i32x4_le_s
  | i32x4_le_u
  | i32x4_ge_s
  | i32x4_ge_u
  | f32x4_eq
  | f32x4_ne
  | f32x4_lt
  | f32x4_gt
  | f32x4_le
  | f32x4_ge
  | f64x2_eq
  | f64x2_ne
  | f64x2_lt
  | f64x2_gt
  | f64x2_le
  | f64x2_ge
  | v128_not
  | v128_and
  | v128_andnot
  | v128_or
  | v128_xor
  | v128_bitselect
  | v128_any_true
  | v128_load8_lane
  | v128_load16_lane
  | v128_load32_lane
  | v128_load64_lane
  | v128_store8_lane
  | v128_store16_lane
  | v128_store32_lane
  | v128_store64_lane
  | v128_load32_zero
  | v128_load64_zero
  | f32x4_demote_f64x2_zero
  | f64x2_promote_low_f32x4
  | i8x16_abs
  | i8x16_neg
  | i8x16_popcnt
  | i8x16_all_true
  | i8x16_bitmask
  | i8x16_narrow_i16x8_s
  | i8x16_narrow_i16x8_u
  | f32x4_ceil
  | f32x4_floor
  | f32x4_trunc
  | f32x4_nearest
  | i8x16_shl
  | i8x16_shr_s
  | i8x16_shr_u
  | i8x16_add
  | i8x16_add_sat_s
  | i8x16_add_sat_u
  | i8x16_sub
  | i8x16_sub_sat_s
  | i8x16_sub_sat_u
  | f64x2_ceil
  | f64x2_floor
  | i8x16_min_s
  | i8x16_min_u
  | i8x16_max_s
  | i8x16_max_u
  | f64x2_trunc
  | i8x16_avgr_u
  | i16x8_extadd_pairwise_i8x16_s
  | i16x8_extadd_pairwise_i8x16_u
  | i32x4_extadd_pairwise_i16x8_s
  | i32x4_extadd_pairwise_i16x8_u
  | i16x8_abs
  | i16x8_neg
  | i16x8_q15mulr_sat_s
  | i16x8_all_true
  | i16x8_bitmask
  | i16x8_narrow_i32x4_s
  | i16x8_narrow_i32x4_u
  | i16x8_extend_low_i8x16_s
  | i16x8_extend_high_i8x16_s
  | i16x8_extend_low_i8x16_u
  | i16x8_extend_high_i8x16_u
  | i16x8_shl
  | i16x8_shr_s
  | i16x8_shr_u
  | i16x8_add
  | i16x8_add_sat_s
  | i16x8_add_sat_u
  | i16x8_sub
  | i16x8_sub_sat_s
  | i16x8_sub_sat_u
  | f64x2_nearest
  | i16x8_mul
  | i16x8_min_s
  | i16x8_min_u
  | i16x8_max_s
  | i16x8_max_u
  | i16x8_avgr_u
  | i16x8_extmul_low_i8x16_s
  | i16x8_extmul_high_i8x16_s
  | i16x8_extmul_low_i8x16_u
  | i16x8_extmul_high_i8x16_u
  | i32x4_abs
  | i32x4_neg
  | i32x4_all_true
  | i32x4_bitmask
  | i32x4_extend_low_i16x8_s
  | i32x4_extend_high_i16x8_s
  | i32x4_extend_low_i16x8_u
  | i32x4_extend_high_i16x8_u
  | i32x4_shl
  | i32x4_shr_s
  | i32x4_shr_u
  | i32x4_add
  | i32x4_sub
  | i32x4_mul
  | i32x4_min_s
  | i32x4_min_u
  | i32x4_max_s
  | i32x4_max_u
  | i32x4_dot_i16x8_s
  | i32x4_extmul_low_i16x8_s
  | i32x4_extmul_high_i16x8_s
  | i32x4_extmul_low_i16x8_u
  | i32x4_extmul_high_i16x8_u
  | i64x2_abs
  | i64x2_neg
  | i64x2_all_true
  | i64x2_bitmask
  | i64x2_extend_low_i32x4_s
  | i64x2_extend_high_i32x4_s
  | i64x2_extend_low_i32x4_u
  | i64x2_extend_high_i32x4_u
  | i64x2_shl
  | i64x2_shr_s
  | i64x2_shr_u
  | i64x2_add
  | i64x2_sub
  | i64x2_mul
  | i64x2_eq
  | i64x2_ne
  | i64x2_lt_s
  | i64x2_gt_s
  | i64x2_le_s
  | i64x2_ge_s
  | i64x2_extmul_low_i32x4_s
  | i64x2_extmul_high_i32x4_s
  | i64x2_extmul_low_i32x4_u
  | i64x2_extmul_high_i32x4_u
  | f32x4_abs
  | f32x4_neg
  | f32x4_sqrt
  | f32x4_add
  | f32x4_sub
  | f32x4_mul
  | f32x4_div
  | f32x4_min
  | f32x4_max
  | f32x4_pmin
  | f32x4_pmax
  | f64x2_abs
  | f64x2_neg
  | f64x2_sqrt
  | f64x2_add
  | f64x2_sub
  | f64x2_mul
  | f64x2_div
  | f64x2_min
  | f64x2_max
  | f64x2_pmin
  | f64x2_pmax
  | i32x4_trunc_sat_f32x4_s
  | i32x4_trunc_sat_f32x4_u
  | f32x4_convert_i32x4_s
  | f32x4_convert_i32x4_u
  | i32x4_trunc_sat_f64x2_s_zero
  | i32x4_trunc_sat_f64x2_u_zero
  | f64x2_convert_low_i32x4_s
  | f64x2_convert_low_i32x4_u
  | i8x16_relaxed_swizzle
  | i32x4_relaxed_trunc_f32x4_s
  | i32x4_relaxed_trunc_f32x4_u
  | i32x4_relaxed_trunc_f64x2_s
  | i32x4_relaxed_trunc_f64x2_u
  | f32x4_relaxed_madd
  | f32x4_relaxed_nmadd
  | f64x2_relaxed_madd
  | f64x2_relaxed_nmadd
  | i8x16_relaxed_laneselect
  | i16x8_relaxed_laneselect
  | i32x4_relaxed_laneselect
  | i64x2_relaxed_laneselect
  | f32x4_relaxed_min
  | f32x4_relaxed_max
  | f64x2_relaxed_min
  | f64x2_relaxed_max
  | i16x8_relaxed_q15mulr_s
  | i16x8_relaxed_dot_i8x16_i7x16_s
  | i32x4_relaxed_dot_i8x16_i7x16_add_s
  deriving DecidableEq, Repr

def VectorOpcode.name : VectorOpcode → String
  | .v128_load => "v128.load"
  | .v128_load8x8_s => "v128.load8x8_s"
  | .v128_load8x8_u => "v128.load8x8_u"
  | .v128_load16x4_s => "v128.load16x4_s"
  | .v128_load16x4_u => "v128.load16x4_u"
  | .v128_load32x2_s => "v128.load32x2_s"
  | .v128_load32x2_u => "v128.load32x2_u"
  | .v128_load8_splat => "v128.load8_splat"
  | .v128_load16_splat => "v128.load16_splat"
  | .v128_load32_splat => "v128.load32_splat"
  | .v128_load64_splat => "v128.load64_splat"
  | .v128_store => "v128.store"
  | .v128_const => "v128.const"
  | .i8x16_shuffle => "i8x16.shuffle"
  | .i8x16_swizzle => "i8x16.swizzle"
  | .i8x16_splat => "i8x16.splat"
  | .i16x8_splat => "i16x8.splat"
  | .i32x4_splat => "i32x4.splat"
  | .i64x2_splat => "i64x2.splat"
  | .f32x4_splat => "f32x4.splat"
  | .f64x2_splat => "f64x2.splat"
  | .i8x16_extract_lane_s => "i8x16.extract_lane_s"
  | .i8x16_extract_lane_u => "i8x16.extract_lane_u"
  | .i8x16_replace_lane => "i8x16.replace_lane"
  | .i16x8_extract_lane_s => "i16x8.extract_lane_s"
  | .i16x8_extract_lane_u => "i16x8.extract_lane_u"
  | .i16x8_replace_lane => "i16x8.replace_lane"
  | .i32x4_extract_lane => "i32x4.extract_lane"
  | .i32x4_replace_lane => "i32x4.replace_lane"
  | .i64x2_extract_lane => "i64x2.extract_lane"
  | .i64x2_replace_lane => "i64x2.replace_lane"
  | .f32x4_extract_lane => "f32x4.extract_lane"
  | .f32x4_replace_lane => "f32x4.replace_lane"
  | .f64x2_extract_lane => "f64x2.extract_lane"
  | .f64x2_replace_lane => "f64x2.replace_lane"
  | .i8x16_eq => "i8x16.eq"
  | .i8x16_ne => "i8x16.ne"
  | .i8x16_lt_s => "i8x16.lt_s"
  | .i8x16_lt_u => "i8x16.lt_u"
  | .i8x16_gt_s => "i8x16.gt_s"
  | .i8x16_gt_u => "i8x16.gt_u"
  | .i8x16_le_s => "i8x16.le_s"
  | .i8x16_le_u => "i8x16.le_u"
  | .i8x16_ge_s => "i8x16.ge_s"
  | .i8x16_ge_u => "i8x16.ge_u"
  | .i16x8_eq => "i16x8.eq"
  | .i16x8_ne => "i16x8.ne"
  | .i16x8_lt_s => "i16x8.lt_s"
  | .i16x8_lt_u => "i16x8.lt_u"
  | .i16x8_gt_s => "i16x8.gt_s"
  | .i16x8_gt_u => "i16x8.gt_u"
  | .i16x8_le_s => "i16x8.le_s"
  | .i16x8_le_u => "i16x8.le_u"
  | .i16x8_ge_s => "i16x8.ge_s"
  | .i16x8_ge_u => "i16x8.ge_u"
  | .i32x4_eq => "i32x4.eq"
  | .i32x4_ne => "i32x4.ne"
  | .i32x4_lt_s => "i32x4.lt_s"
  | .i32x4_lt_u => "i32x4.lt_u"
  | .i32x4_gt_s => "i32x4.gt_s"
  | .i32x4_gt_u => "i32x4.gt_u"
  | .i32x4_le_s => "i32x4.le_s"
  | .i32x4_le_u => "i32x4.le_u"
  | .i32x4_ge_s => "i32x4.ge_s"
  | .i32x4_ge_u => "i32x4.ge_u"
  | .f32x4_eq => "f32x4.eq"
  | .f32x4_ne => "f32x4.ne"
  | .f32x4_lt => "f32x4.lt"
  | .f32x4_gt => "f32x4.gt"
  | .f32x4_le => "f32x4.le"
  | .f32x4_ge => "f32x4.ge"
  | .f64x2_eq => "f64x2.eq"
  | .f64x2_ne => "f64x2.ne"
  | .f64x2_lt => "f64x2.lt"
  | .f64x2_gt => "f64x2.gt"
  | .f64x2_le => "f64x2.le"
  | .f64x2_ge => "f64x2.ge"
  | .v128_not => "v128.not"
  | .v128_and => "v128.and"
  | .v128_andnot => "v128.andnot"
  | .v128_or => "v128.or"
  | .v128_xor => "v128.xor"
  | .v128_bitselect => "v128.bitselect"
  | .v128_any_true => "v128.any_true"
  | .v128_load8_lane => "v128.load8_lane"
  | .v128_load16_lane => "v128.load16_lane"
  | .v128_load32_lane => "v128.load32_lane"
  | .v128_load64_lane => "v128.load64_lane"
  | .v128_store8_lane => "v128.store8_lane"
  | .v128_store16_lane => "v128.store16_lane"
  | .v128_store32_lane => "v128.store32_lane"
  | .v128_store64_lane => "v128.store64_lane"
  | .v128_load32_zero => "v128.load32_zero"
  | .v128_load64_zero => "v128.load64_zero"
  | .f32x4_demote_f64x2_zero => "f32x4.demote_f64x2_zero"
  | .f64x2_promote_low_f32x4 => "f64x2.promote_low_f32x4"
  | .i8x16_abs => "i8x16.abs"
  | .i8x16_neg => "i8x16.neg"
  | .i8x16_popcnt => "i8x16.popcnt"
  | .i8x16_all_true => "i8x16.all_true"
  | .i8x16_bitmask => "i8x16.bitmask"
  | .i8x16_narrow_i16x8_s => "i8x16.narrow_i16x8_s"
  | .i8x16_narrow_i16x8_u => "i8x16.narrow_i16x8_u"
  | .f32x4_ceil => "f32x4.ceil"
  | .f32x4_floor => "f32x4.floor"
  | .f32x4_trunc => "f32x4.trunc"
  | .f32x4_nearest => "f32x4.nearest"
  | .i8x16_shl => "i8x16.shl"
  | .i8x16_shr_s => "i8x16.shr_s"
  | .i8x16_shr_u => "i8x16.shr_u"
  | .i8x16_add => "i8x16.add"
  | .i8x16_add_sat_s => "i8x16.add_sat_s"
  | .i8x16_add_sat_u => "i8x16.add_sat_u"
  | .i8x16_sub => "i8x16.sub"
  | .i8x16_sub_sat_s => "i8x16.sub_sat_s"
  | .i8x16_sub_sat_u => "i8x16.sub_sat_u"
  | .f64x2_ceil => "f64x2.ceil"
  | .f64x2_floor => "f64x2.floor"
  | .i8x16_min_s => "i8x16.min_s"
  | .i8x16_min_u => "i8x16.min_u"
  | .i8x16_max_s => "i8x16.max_s"
  | .i8x16_max_u => "i8x16.max_u"
  | .f64x2_trunc => "f64x2.trunc"
  | .i8x16_avgr_u => "i8x16.avgr_u"
  | .i16x8_extadd_pairwise_i8x16_s => "i16x8.extadd_pairwise_i8x16_s"
  | .i16x8_extadd_pairwise_i8x16_u => "i16x8.extadd_pairwise_i8x16_u"
  | .i32x4_extadd_pairwise_i16x8_s => "i32x4.extadd_pairwise_i16x8_s"
  | .i32x4_extadd_pairwise_i16x8_u => "i32x4.extadd_pairwise_i16x8_u"
  | .i16x8_abs => "i16x8.abs"
  | .i16x8_neg => "i16x8.neg"
  | .i16x8_q15mulr_sat_s => "i16x8.q15mulr_sat_s"
  | .i16x8_all_true => "i16x8.all_true"
  | .i16x8_bitmask => "i16x8.bitmask"
  | .i16x8_narrow_i32x4_s => "i16x8.narrow_i32x4_s"
  | .i16x8_narrow_i32x4_u => "i16x8.narrow_i32x4_u"
  | .i16x8_extend_low_i8x16_s => "i16x8.extend_low_i8x16_s"
  | .i16x8_extend_high_i8x16_s => "i16x8.extend_high_i8x16_s"
  | .i16x8_extend_low_i8x16_u => "i16x8.extend_low_i8x16_u"
  | .i16x8_extend_high_i8x16_u => "i16x8.extend_high_i8x16_u"
  | .i16x8_shl => "i16x8.shl"
  | .i16x8_shr_s => "i16x8.shr_s"
  | .i16x8_shr_u => "i16x8.shr_u"
  | .i16x8_add => "i16x8.add"
  | .i16x8_add_sat_s => "i16x8.add_sat_s"
  | .i16x8_add_sat_u => "i16x8.add_sat_u"
  | .i16x8_sub => "i16x8.sub"
  | .i16x8_sub_sat_s => "i16x8.sub_sat_s"
  | .i16x8_sub_sat_u => "i16x8.sub_sat_u"
  | .f64x2_nearest => "f64x2.nearest"
  | .i16x8_mul => "i16x8.mul"
  | .i16x8_min_s => "i16x8.min_s"
  | .i16x8_min_u => "i16x8.min_u"
  | .i16x8_max_s => "i16x8.max_s"
  | .i16x8_max_u => "i16x8.max_u"
  | .i16x8_avgr_u => "i16x8.avgr_u"
  | .i16x8_extmul_low_i8x16_s => "i16x8.extmul_low_i8x16_s"
  | .i16x8_extmul_high_i8x16_s => "i16x8.extmul_high_i8x16_s"
  | .i16x8_extmul_low_i8x16_u => "i16x8.extmul_low_i8x16_u"
  | .i16x8_extmul_high_i8x16_u => "i16x8.extmul_high_i8x16_u"
  | .i32x4_abs => "i32x4.abs"
  | .i32x4_neg => "i32x4.neg"
  | .i32x4_all_true => "i32x4.all_true"
  | .i32x4_bitmask => "i32x4.bitmask"
  | .i32x4_extend_low_i16x8_s => "i32x4.extend_low_i16x8_s"
  | .i32x4_extend_high_i16x8_s => "i32x4.extend_high_i16x8_s"
  | .i32x4_extend_low_i16x8_u => "i32x4.extend_low_i16x8_u"
  | .i32x4_extend_high_i16x8_u => "i32x4.extend_high_i16x8_u"
  | .i32x4_shl => "i32x4.shl"
  | .i32x4_shr_s => "i32x4.shr_s"
  | .i32x4_shr_u => "i32x4.shr_u"
  | .i32x4_add => "i32x4.add"
  | .i32x4_sub => "i32x4.sub"
  | .i32x4_mul => "i32x4.mul"
  | .i32x4_min_s => "i32x4.min_s"
  | .i32x4_min_u => "i32x4.min_u"
  | .i32x4_max_s => "i32x4.max_s"
  | .i32x4_max_u => "i32x4.max_u"
  | .i32x4_dot_i16x8_s => "i32x4.dot_i16x8_s"
  | .i32x4_extmul_low_i16x8_s => "i32x4.extmul_low_i16x8_s"
  | .i32x4_extmul_high_i16x8_s => "i32x4.extmul_high_i16x8_s"
  | .i32x4_extmul_low_i16x8_u => "i32x4.extmul_low_i16x8_u"
  | .i32x4_extmul_high_i16x8_u => "i32x4.extmul_high_i16x8_u"
  | .i64x2_abs => "i64x2.abs"
  | .i64x2_neg => "i64x2.neg"
  | .i64x2_all_true => "i64x2.all_true"
  | .i64x2_bitmask => "i64x2.bitmask"
  | .i64x2_extend_low_i32x4_s => "i64x2.extend_low_i32x4_s"
  | .i64x2_extend_high_i32x4_s => "i64x2.extend_high_i32x4_s"
  | .i64x2_extend_low_i32x4_u => "i64x2.extend_low_i32x4_u"
  | .i64x2_extend_high_i32x4_u => "i64x2.extend_high_i32x4_u"
  | .i64x2_shl => "i64x2.shl"
  | .i64x2_shr_s => "i64x2.shr_s"
  | .i64x2_shr_u => "i64x2.shr_u"
  | .i64x2_add => "i64x2.add"
  | .i64x2_sub => "i64x2.sub"
  | .i64x2_mul => "i64x2.mul"
  | .i64x2_eq => "i64x2.eq"
  | .i64x2_ne => "i64x2.ne"
  | .i64x2_lt_s => "i64x2.lt_s"
  | .i64x2_gt_s => "i64x2.gt_s"
  | .i64x2_le_s => "i64x2.le_s"
  | .i64x2_ge_s => "i64x2.ge_s"
  | .i64x2_extmul_low_i32x4_s => "i64x2.extmul_low_i32x4_s"
  | .i64x2_extmul_high_i32x4_s => "i64x2.extmul_high_i32x4_s"
  | .i64x2_extmul_low_i32x4_u => "i64x2.extmul_low_i32x4_u"
  | .i64x2_extmul_high_i32x4_u => "i64x2.extmul_high_i32x4_u"
  | .f32x4_abs => "f32x4.abs"
  | .f32x4_neg => "f32x4.neg"
  | .f32x4_sqrt => "f32x4.sqrt"
  | .f32x4_add => "f32x4.add"
  | .f32x4_sub => "f32x4.sub"
  | .f32x4_mul => "f32x4.mul"
  | .f32x4_div => "f32x4.div"
  | .f32x4_min => "f32x4.min"
  | .f32x4_max => "f32x4.max"
  | .f32x4_pmin => "f32x4.pmin"
  | .f32x4_pmax => "f32x4.pmax"
  | .f64x2_abs => "f64x2.abs"
  | .f64x2_neg => "f64x2.neg"
  | .f64x2_sqrt => "f64x2.sqrt"
  | .f64x2_add => "f64x2.add"
  | .f64x2_sub => "f64x2.sub"
  | .f64x2_mul => "f64x2.mul"
  | .f64x2_div => "f64x2.div"
  | .f64x2_min => "f64x2.min"
  | .f64x2_max => "f64x2.max"
  | .f64x2_pmin => "f64x2.pmin"
  | .f64x2_pmax => "f64x2.pmax"
  | .i32x4_trunc_sat_f32x4_s => "i32x4.trunc_sat_f32x4_s"
  | .i32x4_trunc_sat_f32x4_u => "i32x4.trunc_sat_f32x4_u"
  | .f32x4_convert_i32x4_s => "f32x4.convert_i32x4_s"
  | .f32x4_convert_i32x4_u => "f32x4.convert_i32x4_u"
  | .i32x4_trunc_sat_f64x2_s_zero => "i32x4.trunc_sat_f64x2_s_zero"
  | .i32x4_trunc_sat_f64x2_u_zero => "i32x4.trunc_sat_f64x2_u_zero"
  | .f64x2_convert_low_i32x4_s => "f64x2.convert_low_i32x4_s"
  | .f64x2_convert_low_i32x4_u => "f64x2.convert_low_i32x4_u"
  | .i8x16_relaxed_swizzle => "i8x16.relaxed_swizzle"
  | .i32x4_relaxed_trunc_f32x4_s => "i32x4.relaxed_trunc_f32x4_s"
  | .i32x4_relaxed_trunc_f32x4_u => "i32x4.relaxed_trunc_f32x4_u"
  | .i32x4_relaxed_trunc_f64x2_s => "i32x4.relaxed_trunc_f64x2_s_zero"
  | .i32x4_relaxed_trunc_f64x2_u => "i32x4.relaxed_trunc_f64x2_u_zero"
  | .f32x4_relaxed_madd => "f32x4.relaxed_madd"
  | .f32x4_relaxed_nmadd => "f32x4.relaxed_nmadd"
  | .f64x2_relaxed_madd => "f64x2.relaxed_madd"
  | .f64x2_relaxed_nmadd => "f64x2.relaxed_nmadd"
  | .i8x16_relaxed_laneselect => "i8x16.relaxed_laneselect"
  | .i16x8_relaxed_laneselect => "i16x8.relaxed_laneselect"
  | .i32x4_relaxed_laneselect => "i32x4.relaxed_laneselect"
  | .i64x2_relaxed_laneselect => "i64x2.relaxed_laneselect"
  | .f32x4_relaxed_min => "f32x4.relaxed_min"
  | .f32x4_relaxed_max => "f32x4.relaxed_max"
  | .f64x2_relaxed_min => "f64x2.relaxed_min"
  | .f64x2_relaxed_max => "f64x2.relaxed_max"
  | .i16x8_relaxed_q15mulr_s => "i16x8.relaxed_q15mulr_s"
  | .i16x8_relaxed_dot_i8x16_i7x16_s => "i16x8.relaxed_dot_i8x16_i7x16_s"
  | .i32x4_relaxed_dot_i8x16_i7x16_add_s => "i32x4.relaxed_dot_i8x16_i7x16_add_s"

def VectorOpcode.binary : VectorOpcode → Nat
  | .v128_load => 0
  | .v128_load8x8_s => 1
  | .v128_load8x8_u => 2
  | .v128_load16x4_s => 3
  | .v128_load16x4_u => 4
  | .v128_load32x2_s => 5
  | .v128_load32x2_u => 6
  | .v128_load8_splat => 7
  | .v128_load16_splat => 8
  | .v128_load32_splat => 9
  | .v128_load64_splat => 10
  | .v128_store => 11
  | .v128_const => 12
  | .i8x16_shuffle => 13
  | .i8x16_swizzle => 14
  | .i8x16_splat => 15
  | .i16x8_splat => 16
  | .i32x4_splat => 17
  | .i64x2_splat => 18
  | .f32x4_splat => 19
  | .f64x2_splat => 20
  | .i8x16_extract_lane_s => 21
  | .i8x16_extract_lane_u => 22
  | .i8x16_replace_lane => 23
  | .i16x8_extract_lane_s => 24
  | .i16x8_extract_lane_u => 25
  | .i16x8_replace_lane => 26
  | .i32x4_extract_lane => 27
  | .i32x4_replace_lane => 28
  | .i64x2_extract_lane => 29
  | .i64x2_replace_lane => 30
  | .f32x4_extract_lane => 31
  | .f32x4_replace_lane => 32
  | .f64x2_extract_lane => 33
  | .f64x2_replace_lane => 34
  | .i8x16_eq => 35
  | .i8x16_ne => 36
  | .i8x16_lt_s => 37
  | .i8x16_lt_u => 38
  | .i8x16_gt_s => 39
  | .i8x16_gt_u => 40
  | .i8x16_le_s => 41
  | .i8x16_le_u => 42
  | .i8x16_ge_s => 43
  | .i8x16_ge_u => 44
  | .i16x8_eq => 45
  | .i16x8_ne => 46
  | .i16x8_lt_s => 47
  | .i16x8_lt_u => 48
  | .i16x8_gt_s => 49
  | .i16x8_gt_u => 50
  | .i16x8_le_s => 51
  | .i16x8_le_u => 52
  | .i16x8_ge_s => 53
  | .i16x8_ge_u => 54
  | .i32x4_eq => 55
  | .i32x4_ne => 56
  | .i32x4_lt_s => 57
  | .i32x4_lt_u => 58
  | .i32x4_gt_s => 59
  | .i32x4_gt_u => 60
  | .i32x4_le_s => 61
  | .i32x4_le_u => 62
  | .i32x4_ge_s => 63
  | .i32x4_ge_u => 64
  | .f32x4_eq => 65
  | .f32x4_ne => 66
  | .f32x4_lt => 67
  | .f32x4_gt => 68
  | .f32x4_le => 69
  | .f32x4_ge => 70
  | .f64x2_eq => 71
  | .f64x2_ne => 72
  | .f64x2_lt => 73
  | .f64x2_gt => 74
  | .f64x2_le => 75
  | .f64x2_ge => 76
  | .v128_not => 77
  | .v128_and => 78
  | .v128_andnot => 79
  | .v128_or => 80
  | .v128_xor => 81
  | .v128_bitselect => 82
  | .v128_any_true => 83
  | .v128_load8_lane => 84
  | .v128_load16_lane => 85
  | .v128_load32_lane => 86
  | .v128_load64_lane => 87
  | .v128_store8_lane => 88
  | .v128_store16_lane => 89
  | .v128_store32_lane => 90
  | .v128_store64_lane => 91
  | .v128_load32_zero => 92
  | .v128_load64_zero => 93
  | .f32x4_demote_f64x2_zero => 94
  | .f64x2_promote_low_f32x4 => 95
  | .i8x16_abs => 96
  | .i8x16_neg => 97
  | .i8x16_popcnt => 98
  | .i8x16_all_true => 99
  | .i8x16_bitmask => 100
  | .i8x16_narrow_i16x8_s => 101
  | .i8x16_narrow_i16x8_u => 102
  | .f32x4_ceil => 103
  | .f32x4_floor => 104
  | .f32x4_trunc => 105
  | .f32x4_nearest => 106
  | .i8x16_shl => 107
  | .i8x16_shr_s => 108
  | .i8x16_shr_u => 109
  | .i8x16_add => 110
  | .i8x16_add_sat_s => 111
  | .i8x16_add_sat_u => 112
  | .i8x16_sub => 113
  | .i8x16_sub_sat_s => 114
  | .i8x16_sub_sat_u => 115
  | .f64x2_ceil => 116
  | .f64x2_floor => 117
  | .i8x16_min_s => 118
  | .i8x16_min_u => 119
  | .i8x16_max_s => 120
  | .i8x16_max_u => 121
  | .f64x2_trunc => 122
  | .i8x16_avgr_u => 123
  | .i16x8_extadd_pairwise_i8x16_s => 124
  | .i16x8_extadd_pairwise_i8x16_u => 125
  | .i32x4_extadd_pairwise_i16x8_s => 126
  | .i32x4_extadd_pairwise_i16x8_u => 127
  | .i16x8_abs => 128
  | .i16x8_neg => 129
  | .i16x8_q15mulr_sat_s => 130
  | .i16x8_all_true => 131
  | .i16x8_bitmask => 132
  | .i16x8_narrow_i32x4_s => 133
  | .i16x8_narrow_i32x4_u => 134
  | .i16x8_extend_low_i8x16_s => 135
  | .i16x8_extend_high_i8x16_s => 136
  | .i16x8_extend_low_i8x16_u => 137
  | .i16x8_extend_high_i8x16_u => 138
  | .i16x8_shl => 139
  | .i16x8_shr_s => 140
  | .i16x8_shr_u => 141
  | .i16x8_add => 142
  | .i16x8_add_sat_s => 143
  | .i16x8_add_sat_u => 144
  | .i16x8_sub => 145
  | .i16x8_sub_sat_s => 146
  | .i16x8_sub_sat_u => 147
  | .f64x2_nearest => 148
  | .i16x8_mul => 149
  | .i16x8_min_s => 150
  | .i16x8_min_u => 151
  | .i16x8_max_s => 152
  | .i16x8_max_u => 153
  | .i16x8_avgr_u => 155
  | .i16x8_extmul_low_i8x16_s => 156
  | .i16x8_extmul_high_i8x16_s => 157
  | .i16x8_extmul_low_i8x16_u => 158
  | .i16x8_extmul_high_i8x16_u => 159
  | .i32x4_abs => 160
  | .i32x4_neg => 161
  | .i32x4_all_true => 163
  | .i32x4_bitmask => 164
  | .i32x4_extend_low_i16x8_s => 167
  | .i32x4_extend_high_i16x8_s => 168
  | .i32x4_extend_low_i16x8_u => 169
  | .i32x4_extend_high_i16x8_u => 170
  | .i32x4_shl => 171
  | .i32x4_shr_s => 172
  | .i32x4_shr_u => 173
  | .i32x4_add => 174
  | .i32x4_sub => 177
  | .i32x4_mul => 181
  | .i32x4_min_s => 182
  | .i32x4_min_u => 183
  | .i32x4_max_s => 184
  | .i32x4_max_u => 185
  | .i32x4_dot_i16x8_s => 186
  | .i32x4_extmul_low_i16x8_s => 188
  | .i32x4_extmul_high_i16x8_s => 189
  | .i32x4_extmul_low_i16x8_u => 190
  | .i32x4_extmul_high_i16x8_u => 191
  | .i64x2_abs => 192
  | .i64x2_neg => 193
  | .i64x2_all_true => 195
  | .i64x2_bitmask => 196
  | .i64x2_extend_low_i32x4_s => 199
  | .i64x2_extend_high_i32x4_s => 200
  | .i64x2_extend_low_i32x4_u => 201
  | .i64x2_extend_high_i32x4_u => 202
  | .i64x2_shl => 203
  | .i64x2_shr_s => 204
  | .i64x2_shr_u => 205
  | .i64x2_add => 206
  | .i64x2_sub => 209
  | .i64x2_mul => 213
  | .i64x2_eq => 214
  | .i64x2_ne => 215
  | .i64x2_lt_s => 216
  | .i64x2_gt_s => 217
  | .i64x2_le_s => 218
  | .i64x2_ge_s => 219
  | .i64x2_extmul_low_i32x4_s => 220
  | .i64x2_extmul_high_i32x4_s => 221
  | .i64x2_extmul_low_i32x4_u => 222
  | .i64x2_extmul_high_i32x4_u => 223
  | .f32x4_abs => 224
  | .f32x4_neg => 225
  | .f32x4_sqrt => 227
  | .f32x4_add => 228
  | .f32x4_sub => 229
  | .f32x4_mul => 230
  | .f32x4_div => 231
  | .f32x4_min => 232
  | .f32x4_max => 233
  | .f32x4_pmin => 234
  | .f32x4_pmax => 235
  | .f64x2_abs => 236
  | .f64x2_neg => 237
  | .f64x2_sqrt => 239
  | .f64x2_add => 240
  | .f64x2_sub => 241
  | .f64x2_mul => 242
  | .f64x2_div => 243
  | .f64x2_min => 244
  | .f64x2_max => 245
  | .f64x2_pmin => 246
  | .f64x2_pmax => 247
  | .i32x4_trunc_sat_f32x4_s => 248
  | .i32x4_trunc_sat_f32x4_u => 249
  | .f32x4_convert_i32x4_s => 250
  | .f32x4_convert_i32x4_u => 251
  | .i32x4_trunc_sat_f64x2_s_zero => 252
  | .i32x4_trunc_sat_f64x2_u_zero => 253
  | .f64x2_convert_low_i32x4_s => 254
  | .f64x2_convert_low_i32x4_u => 255
  | .i8x16_relaxed_swizzle => 256
  | .i32x4_relaxed_trunc_f32x4_s => 257
  | .i32x4_relaxed_trunc_f32x4_u => 258
  | .i32x4_relaxed_trunc_f64x2_s => 259
  | .i32x4_relaxed_trunc_f64x2_u => 260
  | .f32x4_relaxed_madd => 261
  | .f32x4_relaxed_nmadd => 262
  | .f64x2_relaxed_madd => 263
  | .f64x2_relaxed_nmadd => 264
  | .i8x16_relaxed_laneselect => 265
  | .i16x8_relaxed_laneselect => 266
  | .i32x4_relaxed_laneselect => 267
  | .i64x2_relaxed_laneselect => 268
  | .f32x4_relaxed_min => 269
  | .f32x4_relaxed_max => 270
  | .f64x2_relaxed_min => 271
  | .f64x2_relaxed_max => 272
  | .i16x8_relaxed_q15mulr_s => 273
  | .i16x8_relaxed_dot_i8x16_i7x16_s => 274
  | .i32x4_relaxed_dot_i8x16_i7x16_add_s => 275

private def opcodeName0 : String → Option VectorOpcode
  | "v128.load" => some .v128_load
  | "v128.load8x8_s" => some .v128_load8x8_s
  | "v128.load8x8_u" => some .v128_load8x8_u
  | "v128.load16x4_s" => some .v128_load16x4_s
  | "v128.load16x4_u" => some .v128_load16x4_u
  | "v128.load32x2_s" => some .v128_load32x2_s
  | "v128.load32x2_u" => some .v128_load32x2_u
  | "v128.load8_splat" => some .v128_load8_splat
  | "v128.load16_splat" => some .v128_load16_splat
  | "v128.load32_splat" => some .v128_load32_splat
  | "v128.load64_splat" => some .v128_load64_splat
  | "v128.store" => some .v128_store
  | "v128.const" => some .v128_const
  | "i8x16.shuffle" => some .i8x16_shuffle
  | "i8x16.swizzle" => some .i8x16_swizzle
  | "i8x16.splat" => some .i8x16_splat
  | "i16x8.splat" => some .i16x8_splat
  | "i32x4.splat" => some .i32x4_splat
  | "i64x2.splat" => some .i64x2_splat
  | "f32x4.splat" => some .f32x4_splat
  | "f64x2.splat" => some .f64x2_splat
  | "i8x16.extract_lane_s" => some .i8x16_extract_lane_s
  | "i8x16.extract_lane_u" => some .i8x16_extract_lane_u
  | "i8x16.replace_lane" => some .i8x16_replace_lane
  | "i16x8.extract_lane_s" => some .i16x8_extract_lane_s
  | "i16x8.extract_lane_u" => some .i16x8_extract_lane_u
  | "i16x8.replace_lane" => some .i16x8_replace_lane
  | "i32x4.extract_lane" => some .i32x4_extract_lane
  | "i32x4.replace_lane" => some .i32x4_replace_lane
  | "i64x2.extract_lane" => some .i64x2_extract_lane
  | "i64x2.replace_lane" => some .i64x2_replace_lane
  | "f32x4.extract_lane" => some .f32x4_extract_lane
  | "f32x4.replace_lane" => some .f32x4_replace_lane
  | "f64x2.extract_lane" => some .f64x2_extract_lane
  | "f64x2.replace_lane" => some .f64x2_replace_lane
  | "i8x16.eq" => some .i8x16_eq
  | "i8x16.ne" => some .i8x16_ne
  | "i8x16.lt_s" => some .i8x16_lt_s
  | "i8x16.lt_u" => some .i8x16_lt_u
  | "i8x16.gt_s" => some .i8x16_gt_s
  | "i8x16.gt_u" => some .i8x16_gt_u
  | "i8x16.le_s" => some .i8x16_le_s
  | "i8x16.le_u" => some .i8x16_le_u
  | "i8x16.ge_s" => some .i8x16_ge_s
  | "i8x16.ge_u" => some .i8x16_ge_u
  | "i16x8.eq" => some .i16x8_eq
  | "i16x8.ne" => some .i16x8_ne
  | "i16x8.lt_s" => some .i16x8_lt_s
  | "i16x8.lt_u" => some .i16x8_lt_u
  | "i16x8.gt_s" => some .i16x8_gt_s
  | "i16x8.gt_u" => some .i16x8_gt_u
  | "i16x8.le_s" => some .i16x8_le_s
  | "i16x8.le_u" => some .i16x8_le_u
  | "i16x8.ge_s" => some .i16x8_ge_s
  | "i16x8.ge_u" => some .i16x8_ge_u
  | "i32x4.eq" => some .i32x4_eq
  | "i32x4.ne" => some .i32x4_ne
  | "i32x4.lt_s" => some .i32x4_lt_s
  | "i32x4.lt_u" => some .i32x4_lt_u
  | "i32x4.gt_s" => some .i32x4_gt_s
  | "i32x4.gt_u" => some .i32x4_gt_u
  | "i32x4.le_s" => some .i32x4_le_s
  | "i32x4.le_u" => some .i32x4_le_u
  | "i32x4.ge_s" => some .i32x4_ge_s
  | _ => none

private def opcodeName1 : String → Option VectorOpcode
  | "i32x4.ge_u" => some .i32x4_ge_u
  | "f32x4.eq" => some .f32x4_eq
  | "f32x4.ne" => some .f32x4_ne
  | "f32x4.lt" => some .f32x4_lt
  | "f32x4.gt" => some .f32x4_gt
  | "f32x4.le" => some .f32x4_le
  | "f32x4.ge" => some .f32x4_ge
  | "f64x2.eq" => some .f64x2_eq
  | "f64x2.ne" => some .f64x2_ne
  | "f64x2.lt" => some .f64x2_lt
  | "f64x2.gt" => some .f64x2_gt
  | "f64x2.le" => some .f64x2_le
  | "f64x2.ge" => some .f64x2_ge
  | "v128.not" => some .v128_not
  | "v128.and" => some .v128_and
  | "v128.andnot" => some .v128_andnot
  | "v128.or" => some .v128_or
  | "v128.xor" => some .v128_xor
  | "v128.bitselect" => some .v128_bitselect
  | "v128.any_true" => some .v128_any_true
  | "v128.load8_lane" => some .v128_load8_lane
  | "v128.load16_lane" => some .v128_load16_lane
  | "v128.load32_lane" => some .v128_load32_lane
  | "v128.load64_lane" => some .v128_load64_lane
  | "v128.store8_lane" => some .v128_store8_lane
  | "v128.store16_lane" => some .v128_store16_lane
  | "v128.store32_lane" => some .v128_store32_lane
  | "v128.store64_lane" => some .v128_store64_lane
  | "v128.load32_zero" => some .v128_load32_zero
  | "v128.load64_zero" => some .v128_load64_zero
  | "f32x4.demote_f64x2_zero" => some .f32x4_demote_f64x2_zero
  | "f64x2.promote_low_f32x4" => some .f64x2_promote_low_f32x4
  | "i8x16.abs" => some .i8x16_abs
  | "i8x16.neg" => some .i8x16_neg
  | "i8x16.popcnt" => some .i8x16_popcnt
  | "i8x16.all_true" => some .i8x16_all_true
  | "i8x16.bitmask" => some .i8x16_bitmask
  | "i8x16.narrow_i16x8_s" => some .i8x16_narrow_i16x8_s
  | "i8x16.narrow_i16x8_u" => some .i8x16_narrow_i16x8_u
  | "f32x4.ceil" => some .f32x4_ceil
  | "f32x4.floor" => some .f32x4_floor
  | "f32x4.trunc" => some .f32x4_trunc
  | "f32x4.nearest" => some .f32x4_nearest
  | "i8x16.shl" => some .i8x16_shl
  | "i8x16.shr_s" => some .i8x16_shr_s
  | "i8x16.shr_u" => some .i8x16_shr_u
  | "i8x16.add" => some .i8x16_add
  | "i8x16.add_sat_s" => some .i8x16_add_sat_s
  | "i8x16.add_sat_u" => some .i8x16_add_sat_u
  | "i8x16.sub" => some .i8x16_sub
  | "i8x16.sub_sat_s" => some .i8x16_sub_sat_s
  | "i8x16.sub_sat_u" => some .i8x16_sub_sat_u
  | "f64x2.ceil" => some .f64x2_ceil
  | "f64x2.floor" => some .f64x2_floor
  | "i8x16.min_s" => some .i8x16_min_s
  | "i8x16.min_u" => some .i8x16_min_u
  | "i8x16.max_s" => some .i8x16_max_s
  | "i8x16.max_u" => some .i8x16_max_u
  | "f64x2.trunc" => some .f64x2_trunc
  | "i8x16.avgr_u" => some .i8x16_avgr_u
  | "i16x8.extadd_pairwise_i8x16_s" => some .i16x8_extadd_pairwise_i8x16_s
  | "i16x8.extadd_pairwise_i8x16_u" => some .i16x8_extadd_pairwise_i8x16_u
  | "i32x4.extadd_pairwise_i16x8_s" => some .i32x4_extadd_pairwise_i16x8_s
  | "i32x4.extadd_pairwise_i16x8_u" => some .i32x4_extadd_pairwise_i16x8_u
  | _ => none

private def opcodeName2 : String → Option VectorOpcode
  | "i16x8.abs" => some .i16x8_abs
  | "i16x8.neg" => some .i16x8_neg
  | "i16x8.q15mulr_sat_s" => some .i16x8_q15mulr_sat_s
  | "i16x8.all_true" => some .i16x8_all_true
  | "i16x8.bitmask" => some .i16x8_bitmask
  | "i16x8.narrow_i32x4_s" => some .i16x8_narrow_i32x4_s
  | "i16x8.narrow_i32x4_u" => some .i16x8_narrow_i32x4_u
  | "i16x8.extend_low_i8x16_s" => some .i16x8_extend_low_i8x16_s
  | "i16x8.extend_high_i8x16_s" => some .i16x8_extend_high_i8x16_s
  | "i16x8.extend_low_i8x16_u" => some .i16x8_extend_low_i8x16_u
  | "i16x8.extend_high_i8x16_u" => some .i16x8_extend_high_i8x16_u
  | "i16x8.shl" => some .i16x8_shl
  | "i16x8.shr_s" => some .i16x8_shr_s
  | "i16x8.shr_u" => some .i16x8_shr_u
  | "i16x8.add" => some .i16x8_add
  | "i16x8.add_sat_s" => some .i16x8_add_sat_s
  | "i16x8.add_sat_u" => some .i16x8_add_sat_u
  | "i16x8.sub" => some .i16x8_sub
  | "i16x8.sub_sat_s" => some .i16x8_sub_sat_s
  | "i16x8.sub_sat_u" => some .i16x8_sub_sat_u
  | "f64x2.nearest" => some .f64x2_nearest
  | "i16x8.mul" => some .i16x8_mul
  | "i16x8.min_s" => some .i16x8_min_s
  | "i16x8.min_u" => some .i16x8_min_u
  | "i16x8.max_s" => some .i16x8_max_s
  | "i16x8.max_u" => some .i16x8_max_u
  | "i16x8.avgr_u" => some .i16x8_avgr_u
  | "i16x8.extmul_low_i8x16_s" => some .i16x8_extmul_low_i8x16_s
  | "i16x8.extmul_high_i8x16_s" => some .i16x8_extmul_high_i8x16_s
  | "i16x8.extmul_low_i8x16_u" => some .i16x8_extmul_low_i8x16_u
  | "i16x8.extmul_high_i8x16_u" => some .i16x8_extmul_high_i8x16_u
  | "i32x4.abs" => some .i32x4_abs
  | "i32x4.neg" => some .i32x4_neg
  | "i32x4.all_true" => some .i32x4_all_true
  | "i32x4.bitmask" => some .i32x4_bitmask
  | "i32x4.extend_low_i16x8_s" => some .i32x4_extend_low_i16x8_s
  | "i32x4.extend_high_i16x8_s" => some .i32x4_extend_high_i16x8_s
  | "i32x4.extend_low_i16x8_u" => some .i32x4_extend_low_i16x8_u
  | "i32x4.extend_high_i16x8_u" => some .i32x4_extend_high_i16x8_u
  | "i32x4.shl" => some .i32x4_shl
  | "i32x4.shr_s" => some .i32x4_shr_s
  | "i32x4.shr_u" => some .i32x4_shr_u
  | "i32x4.add" => some .i32x4_add
  | "i32x4.sub" => some .i32x4_sub
  | "i32x4.mul" => some .i32x4_mul
  | "i32x4.min_s" => some .i32x4_min_s
  | "i32x4.min_u" => some .i32x4_min_u
  | "i32x4.max_s" => some .i32x4_max_s
  | "i32x4.max_u" => some .i32x4_max_u
  | "i32x4.dot_i16x8_s" => some .i32x4_dot_i16x8_s
  | "i32x4.extmul_low_i16x8_s" => some .i32x4_extmul_low_i16x8_s
  | "i32x4.extmul_high_i16x8_s" => some .i32x4_extmul_high_i16x8_s
  | "i32x4.extmul_low_i16x8_u" => some .i32x4_extmul_low_i16x8_u
  | "i32x4.extmul_high_i16x8_u" => some .i32x4_extmul_high_i16x8_u
  | "i64x2.abs" => some .i64x2_abs
  | "i64x2.neg" => some .i64x2_neg
  | "i64x2.all_true" => some .i64x2_all_true
  | "i64x2.bitmask" => some .i64x2_bitmask
  | "i64x2.extend_low_i32x4_s" => some .i64x2_extend_low_i32x4_s
  | "i64x2.extend_high_i32x4_s" => some .i64x2_extend_high_i32x4_s
  | "i64x2.extend_low_i32x4_u" => some .i64x2_extend_low_i32x4_u
  | "i64x2.extend_high_i32x4_u" => some .i64x2_extend_high_i32x4_u
  | "i64x2.shl" => some .i64x2_shl
  | "i64x2.shr_s" => some .i64x2_shr_s
  | _ => none

private def opcodeName3 : String → Option VectorOpcode
  | "i64x2.shr_u" => some .i64x2_shr_u
  | "i64x2.add" => some .i64x2_add
  | "i64x2.sub" => some .i64x2_sub
  | "i64x2.mul" => some .i64x2_mul
  | "i64x2.eq" => some .i64x2_eq
  | "i64x2.ne" => some .i64x2_ne
  | "i64x2.lt_s" => some .i64x2_lt_s
  | "i64x2.gt_s" => some .i64x2_gt_s
  | "i64x2.le_s" => some .i64x2_le_s
  | "i64x2.ge_s" => some .i64x2_ge_s
  | "i64x2.extmul_low_i32x4_s" => some .i64x2_extmul_low_i32x4_s
  | "i64x2.extmul_high_i32x4_s" => some .i64x2_extmul_high_i32x4_s
  | "i64x2.extmul_low_i32x4_u" => some .i64x2_extmul_low_i32x4_u
  | "i64x2.extmul_high_i32x4_u" => some .i64x2_extmul_high_i32x4_u
  | "f32x4.abs" => some .f32x4_abs
  | "f32x4.neg" => some .f32x4_neg
  | "f32x4.sqrt" => some .f32x4_sqrt
  | "f32x4.add" => some .f32x4_add
  | "f32x4.sub" => some .f32x4_sub
  | "f32x4.mul" => some .f32x4_mul
  | "f32x4.div" => some .f32x4_div
  | "f32x4.min" => some .f32x4_min
  | "f32x4.max" => some .f32x4_max
  | "f32x4.pmin" => some .f32x4_pmin
  | "f32x4.pmax" => some .f32x4_pmax
  | "f64x2.abs" => some .f64x2_abs
  | "f64x2.neg" => some .f64x2_neg
  | "f64x2.sqrt" => some .f64x2_sqrt
  | "f64x2.add" => some .f64x2_add
  | "f64x2.sub" => some .f64x2_sub
  | "f64x2.mul" => some .f64x2_mul
  | "f64x2.div" => some .f64x2_div
  | "f64x2.min" => some .f64x2_min
  | "f64x2.max" => some .f64x2_max
  | "f64x2.pmin" => some .f64x2_pmin
  | "f64x2.pmax" => some .f64x2_pmax
  | "i32x4.trunc_sat_f32x4_s" => some .i32x4_trunc_sat_f32x4_s
  | "i32x4.trunc_sat_f32x4_u" => some .i32x4_trunc_sat_f32x4_u
  | "f32x4.convert_i32x4_s" => some .f32x4_convert_i32x4_s
  | "f32x4.convert_i32x4_u" => some .f32x4_convert_i32x4_u
  | "i32x4.trunc_sat_f64x2_s_zero" => some .i32x4_trunc_sat_f64x2_s_zero
  | "i32x4.trunc_sat_f64x2_u_zero" => some .i32x4_trunc_sat_f64x2_u_zero
  | "f64x2.convert_low_i32x4_s" => some .f64x2_convert_low_i32x4_s
  | "f64x2.convert_low_i32x4_u" => some .f64x2_convert_low_i32x4_u
  | "i8x16.relaxed_swizzle" => some .i8x16_relaxed_swizzle
  | "i32x4.relaxed_trunc_f32x4_s" => some .i32x4_relaxed_trunc_f32x4_s
  | "i32x4.relaxed_trunc_f32x4_u" => some .i32x4_relaxed_trunc_f32x4_u
  | "i32x4.relaxed_trunc_f64x2_s_zero" => some .i32x4_relaxed_trunc_f64x2_s
  | "i32x4.relaxed_trunc_f64x2_u_zero" => some .i32x4_relaxed_trunc_f64x2_u
  | "f32x4.relaxed_madd" => some .f32x4_relaxed_madd
  | "f32x4.relaxed_nmadd" => some .f32x4_relaxed_nmadd
  | "f64x2.relaxed_madd" => some .f64x2_relaxed_madd
  | "f64x2.relaxed_nmadd" => some .f64x2_relaxed_nmadd
  | "i8x16.relaxed_laneselect" => some .i8x16_relaxed_laneselect
  | "i16x8.relaxed_laneselect" => some .i16x8_relaxed_laneselect
  | "i32x4.relaxed_laneselect" => some .i32x4_relaxed_laneselect
  | "i64x2.relaxed_laneselect" => some .i64x2_relaxed_laneselect
  | "f32x4.relaxed_min" => some .f32x4_relaxed_min
  | "f32x4.relaxed_max" => some .f32x4_relaxed_max
  | "f64x2.relaxed_min" => some .f64x2_relaxed_min
  | "f64x2.relaxed_max" => some .f64x2_relaxed_max
  | "i16x8.relaxed_q15mulr_s" => some .i16x8_relaxed_q15mulr_s
  | "i16x8.relaxed_dot_i8x16_i7x16_s" => some .i16x8_relaxed_dot_i8x16_i7x16_s
  | "i32x4.relaxed_dot_i8x16_i7x16_add_s" => some .i32x4_relaxed_dot_i8x16_i7x16_add_s
  | _ => none

def VectorOpcode.ofName (name : String) : Option VectorOpcode :=
  opcodeName0 name <|> opcodeName1 name <|> opcodeName2 name <|> opcodeName3 name

private def opcodeBinary0 : Nat → Option VectorOpcode
  | 0 => some .v128_load
  | 1 => some .v128_load8x8_s
  | 2 => some .v128_load8x8_u
  | 3 => some .v128_load16x4_s
  | 4 => some .v128_load16x4_u
  | 5 => some .v128_load32x2_s
  | 6 => some .v128_load32x2_u
  | 7 => some .v128_load8_splat
  | 8 => some .v128_load16_splat
  | 9 => some .v128_load32_splat
  | 10 => some .v128_load64_splat
  | 11 => some .v128_store
  | 12 => some .v128_const
  | 13 => some .i8x16_shuffle
  | 14 => some .i8x16_swizzle
  | 15 => some .i8x16_splat
  | 16 => some .i16x8_splat
  | 17 => some .i32x4_splat
  | 18 => some .i64x2_splat
  | 19 => some .f32x4_splat
  | 20 => some .f64x2_splat
  | 21 => some .i8x16_extract_lane_s
  | 22 => some .i8x16_extract_lane_u
  | 23 => some .i8x16_replace_lane
  | 24 => some .i16x8_extract_lane_s
  | 25 => some .i16x8_extract_lane_u
  | 26 => some .i16x8_replace_lane
  | 27 => some .i32x4_extract_lane
  | 28 => some .i32x4_replace_lane
  | 29 => some .i64x2_extract_lane
  | 30 => some .i64x2_replace_lane
  | 31 => some .f32x4_extract_lane
  | 32 => some .f32x4_replace_lane
  | 33 => some .f64x2_extract_lane
  | 34 => some .f64x2_replace_lane
  | 35 => some .i8x16_eq
  | 36 => some .i8x16_ne
  | 37 => some .i8x16_lt_s
  | 38 => some .i8x16_lt_u
  | 39 => some .i8x16_gt_s
  | 40 => some .i8x16_gt_u
  | 41 => some .i8x16_le_s
  | 42 => some .i8x16_le_u
  | 43 => some .i8x16_ge_s
  | 44 => some .i8x16_ge_u
  | 45 => some .i16x8_eq
  | 46 => some .i16x8_ne
  | 47 => some .i16x8_lt_s
  | 48 => some .i16x8_lt_u
  | 49 => some .i16x8_gt_s
  | 50 => some .i16x8_gt_u
  | 51 => some .i16x8_le_s
  | 52 => some .i16x8_le_u
  | 53 => some .i16x8_ge_s
  | 54 => some .i16x8_ge_u
  | 55 => some .i32x4_eq
  | 56 => some .i32x4_ne
  | 57 => some .i32x4_lt_s
  | 58 => some .i32x4_lt_u
  | 59 => some .i32x4_gt_s
  | 60 => some .i32x4_gt_u
  | 61 => some .i32x4_le_s
  | 62 => some .i32x4_le_u
  | 63 => some .i32x4_ge_s
  | _ => none

private def opcodeBinary1 : Nat → Option VectorOpcode
  | 64 => some .i32x4_ge_u
  | 65 => some .f32x4_eq
  | 66 => some .f32x4_ne
  | 67 => some .f32x4_lt
  | 68 => some .f32x4_gt
  | 69 => some .f32x4_le
  | 70 => some .f32x4_ge
  | 71 => some .f64x2_eq
  | 72 => some .f64x2_ne
  | 73 => some .f64x2_lt
  | 74 => some .f64x2_gt
  | 75 => some .f64x2_le
  | 76 => some .f64x2_ge
  | 77 => some .v128_not
  | 78 => some .v128_and
  | 79 => some .v128_andnot
  | 80 => some .v128_or
  | 81 => some .v128_xor
  | 82 => some .v128_bitselect
  | 83 => some .v128_any_true
  | 84 => some .v128_load8_lane
  | 85 => some .v128_load16_lane
  | 86 => some .v128_load32_lane
  | 87 => some .v128_load64_lane
  | 88 => some .v128_store8_lane
  | 89 => some .v128_store16_lane
  | 90 => some .v128_store32_lane
  | 91 => some .v128_store64_lane
  | 92 => some .v128_load32_zero
  | 93 => some .v128_load64_zero
  | 94 => some .f32x4_demote_f64x2_zero
  | 95 => some .f64x2_promote_low_f32x4
  | 96 => some .i8x16_abs
  | 97 => some .i8x16_neg
  | 98 => some .i8x16_popcnt
  | 99 => some .i8x16_all_true
  | 100 => some .i8x16_bitmask
  | 101 => some .i8x16_narrow_i16x8_s
  | 102 => some .i8x16_narrow_i16x8_u
  | 103 => some .f32x4_ceil
  | 104 => some .f32x4_floor
  | 105 => some .f32x4_trunc
  | 106 => some .f32x4_nearest
  | 107 => some .i8x16_shl
  | 108 => some .i8x16_shr_s
  | 109 => some .i8x16_shr_u
  | 110 => some .i8x16_add
  | 111 => some .i8x16_add_sat_s
  | 112 => some .i8x16_add_sat_u
  | 113 => some .i8x16_sub
  | 114 => some .i8x16_sub_sat_s
  | 115 => some .i8x16_sub_sat_u
  | 116 => some .f64x2_ceil
  | 117 => some .f64x2_floor
  | 118 => some .i8x16_min_s
  | 119 => some .i8x16_min_u
  | 120 => some .i8x16_max_s
  | 121 => some .i8x16_max_u
  | 122 => some .f64x2_trunc
  | 123 => some .i8x16_avgr_u
  | 124 => some .i16x8_extadd_pairwise_i8x16_s
  | 125 => some .i16x8_extadd_pairwise_i8x16_u
  | 126 => some .i32x4_extadd_pairwise_i16x8_s
  | 127 => some .i32x4_extadd_pairwise_i16x8_u
  | _ => none

private def opcodeBinary2 : Nat → Option VectorOpcode
  | 128 => some .i16x8_abs
  | 129 => some .i16x8_neg
  | 130 => some .i16x8_q15mulr_sat_s
  | 131 => some .i16x8_all_true
  | 132 => some .i16x8_bitmask
  | 133 => some .i16x8_narrow_i32x4_s
  | 134 => some .i16x8_narrow_i32x4_u
  | 135 => some .i16x8_extend_low_i8x16_s
  | 136 => some .i16x8_extend_high_i8x16_s
  | 137 => some .i16x8_extend_low_i8x16_u
  | 138 => some .i16x8_extend_high_i8x16_u
  | 139 => some .i16x8_shl
  | 140 => some .i16x8_shr_s
  | 141 => some .i16x8_shr_u
  | 142 => some .i16x8_add
  | 143 => some .i16x8_add_sat_s
  | 144 => some .i16x8_add_sat_u
  | 145 => some .i16x8_sub
  | 146 => some .i16x8_sub_sat_s
  | 147 => some .i16x8_sub_sat_u
  | 148 => some .f64x2_nearest
  | 149 => some .i16x8_mul
  | 150 => some .i16x8_min_s
  | 151 => some .i16x8_min_u
  | 152 => some .i16x8_max_s
  | 153 => some .i16x8_max_u
  | 155 => some .i16x8_avgr_u
  | 156 => some .i16x8_extmul_low_i8x16_s
  | 157 => some .i16x8_extmul_high_i8x16_s
  | 158 => some .i16x8_extmul_low_i8x16_u
  | 159 => some .i16x8_extmul_high_i8x16_u
  | 160 => some .i32x4_abs
  | 161 => some .i32x4_neg
  | 163 => some .i32x4_all_true
  | 164 => some .i32x4_bitmask
  | 167 => some .i32x4_extend_low_i16x8_s
  | 168 => some .i32x4_extend_high_i16x8_s
  | 169 => some .i32x4_extend_low_i16x8_u
  | 170 => some .i32x4_extend_high_i16x8_u
  | 171 => some .i32x4_shl
  | 172 => some .i32x4_shr_s
  | 173 => some .i32x4_shr_u
  | 174 => some .i32x4_add
  | 177 => some .i32x4_sub
  | 181 => some .i32x4_mul
  | 182 => some .i32x4_min_s
  | 183 => some .i32x4_min_u
  | 184 => some .i32x4_max_s
  | 185 => some .i32x4_max_u
  | 186 => some .i32x4_dot_i16x8_s
  | 188 => some .i32x4_extmul_low_i16x8_s
  | 189 => some .i32x4_extmul_high_i16x8_s
  | 190 => some .i32x4_extmul_low_i16x8_u
  | 191 => some .i32x4_extmul_high_i16x8_u
  | 192 => some .i64x2_abs
  | 193 => some .i64x2_neg
  | 195 => some .i64x2_all_true
  | 196 => some .i64x2_bitmask
  | 199 => some .i64x2_extend_low_i32x4_s
  | 200 => some .i64x2_extend_high_i32x4_s
  | 201 => some .i64x2_extend_low_i32x4_u
  | 202 => some .i64x2_extend_high_i32x4_u
  | 203 => some .i64x2_shl
  | 204 => some .i64x2_shr_s
  | _ => none

private def opcodeBinary3 : Nat → Option VectorOpcode
  | 205 => some .i64x2_shr_u
  | 206 => some .i64x2_add
  | 209 => some .i64x2_sub
  | 213 => some .i64x2_mul
  | 214 => some .i64x2_eq
  | 215 => some .i64x2_ne
  | 216 => some .i64x2_lt_s
  | 217 => some .i64x2_gt_s
  | 218 => some .i64x2_le_s
  | 219 => some .i64x2_ge_s
  | 220 => some .i64x2_extmul_low_i32x4_s
  | 221 => some .i64x2_extmul_high_i32x4_s
  | 222 => some .i64x2_extmul_low_i32x4_u
  | 223 => some .i64x2_extmul_high_i32x4_u
  | 224 => some .f32x4_abs
  | 225 => some .f32x4_neg
  | 227 => some .f32x4_sqrt
  | 228 => some .f32x4_add
  | 229 => some .f32x4_sub
  | 230 => some .f32x4_mul
  | 231 => some .f32x4_div
  | 232 => some .f32x4_min
  | 233 => some .f32x4_max
  | 234 => some .f32x4_pmin
  | 235 => some .f32x4_pmax
  | 236 => some .f64x2_abs
  | 237 => some .f64x2_neg
  | 239 => some .f64x2_sqrt
  | 240 => some .f64x2_add
  | 241 => some .f64x2_sub
  | 242 => some .f64x2_mul
  | 243 => some .f64x2_div
  | 244 => some .f64x2_min
  | 245 => some .f64x2_max
  | 246 => some .f64x2_pmin
  | 247 => some .f64x2_pmax
  | 248 => some .i32x4_trunc_sat_f32x4_s
  | 249 => some .i32x4_trunc_sat_f32x4_u
  | 250 => some .f32x4_convert_i32x4_s
  | 251 => some .f32x4_convert_i32x4_u
  | 252 => some .i32x4_trunc_sat_f64x2_s_zero
  | 253 => some .i32x4_trunc_sat_f64x2_u_zero
  | 254 => some .f64x2_convert_low_i32x4_s
  | 255 => some .f64x2_convert_low_i32x4_u
  | 256 => some .i8x16_relaxed_swizzle
  | 257 => some .i32x4_relaxed_trunc_f32x4_s
  | 258 => some .i32x4_relaxed_trunc_f32x4_u
  | 259 => some .i32x4_relaxed_trunc_f64x2_s
  | 260 => some .i32x4_relaxed_trunc_f64x2_u
  | 261 => some .f32x4_relaxed_madd
  | 262 => some .f32x4_relaxed_nmadd
  | 263 => some .f64x2_relaxed_madd
  | 264 => some .f64x2_relaxed_nmadd
  | 265 => some .i8x16_relaxed_laneselect
  | 266 => some .i16x8_relaxed_laneselect
  | 267 => some .i32x4_relaxed_laneselect
  | 268 => some .i64x2_relaxed_laneselect
  | 269 => some .f32x4_relaxed_min
  | 270 => some .f32x4_relaxed_max
  | 271 => some .f64x2_relaxed_min
  | 272 => some .f64x2_relaxed_max
  | 273 => some .i16x8_relaxed_q15mulr_s
  | 274 => some .i16x8_relaxed_dot_i8x16_i7x16_s
  | 275 => some .i32x4_relaxed_dot_i8x16_i7x16_add_s
  | _ => none

def VectorOpcode.ofBinary (code : Nat) : Option VectorOpcode :=
  opcodeBinary0 code <|> opcodeBinary1 code <|> opcodeBinary2 code <|> opcodeBinary3 code

end Wasm
