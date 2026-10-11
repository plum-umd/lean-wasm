import Wasm.MemoryValidation

namespace Wasm

def VectorOpcode.signature (address : ValType := .i32) : VectorOpcode → FuncType
  | .v128_load => ⟨[address], [.v128]⟩
  | .v128_load8x8_s => ⟨[address], [.v128]⟩
  | .v128_load8x8_u => ⟨[address], [.v128]⟩
  | .v128_load16x4_s => ⟨[address], [.v128]⟩
  | .v128_load16x4_u => ⟨[address], [.v128]⟩
  | .v128_load32x2_s => ⟨[address], [.v128]⟩
  | .v128_load32x2_u => ⟨[address], [.v128]⟩
  | .v128_load8_splat => ⟨[address], [.v128]⟩
  | .v128_load16_splat => ⟨[address], [.v128]⟩
  | .v128_load32_splat => ⟨[address], [.v128]⟩
  | .v128_load64_splat => ⟨[address], [.v128]⟩
  | .v128_store => ⟨[address, .v128], []⟩
  | .v128_const => ⟨[], [.v128]⟩
  | .i8x16_shuffle => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_swizzle => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_splat => ⟨[.i32], [.v128]⟩
  | .i16x8_splat => ⟨[.i32], [.v128]⟩
  | .i32x4_splat => ⟨[.i32], [.v128]⟩
  | .i64x2_splat => ⟨[.i64], [.v128]⟩
  | .f32x4_splat => ⟨[.f32], [.v128]⟩
  | .f64x2_splat => ⟨[.f64], [.v128]⟩
  | .i8x16_extract_lane_s => ⟨[.v128], [.i32]⟩
  | .i8x16_extract_lane_u => ⟨[.v128], [.i32]⟩
  | .i8x16_replace_lane => ⟨[.v128, .i32], [.v128]⟩
  | .i16x8_extract_lane_s => ⟨[.v128], [.i32]⟩
  | .i16x8_extract_lane_u => ⟨[.v128], [.i32]⟩
  | .i16x8_replace_lane => ⟨[.v128, .i32], [.v128]⟩
  | .i32x4_extract_lane => ⟨[.v128], [.i32]⟩
  | .i32x4_replace_lane => ⟨[.v128, .i32], [.v128]⟩
  | .i64x2_extract_lane => ⟨[.v128], [.i64]⟩
  | .i64x2_replace_lane => ⟨[.v128, .i64], [.v128]⟩
  | .f32x4_extract_lane => ⟨[.v128], [.f32]⟩
  | .f32x4_replace_lane => ⟨[.v128, .f32], [.v128]⟩
  | .f64x2_extract_lane => ⟨[.v128], [.f64]⟩
  | .f64x2_replace_lane => ⟨[.v128, .f64], [.v128]⟩
  | .i8x16_eq => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_ne => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_lt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_lt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_gt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_gt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_le_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_le_u => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_ge_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_ge_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_eq => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_ne => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_lt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_lt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_gt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_gt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_le_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_le_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_ge_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_ge_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_eq => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_ne => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_lt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_lt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_gt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_gt_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_le_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_le_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_ge_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_ge_u => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_eq => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_ne => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_lt => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_gt => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_le => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_ge => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_eq => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_ne => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_lt => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_gt => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_le => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_ge => ⟨[.v128, .v128], [.v128]⟩
  | .v128_not => ⟨[.v128], [.v128]⟩
  | .v128_and => ⟨[.v128, .v128], [.v128]⟩
  | .v128_andnot => ⟨[.v128, .v128], [.v128]⟩
  | .v128_or => ⟨[.v128, .v128], [.v128]⟩
  | .v128_xor => ⟨[.v128, .v128], [.v128]⟩
  | .v128_bitselect => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .v128_any_true => ⟨[.v128], [.i32]⟩
  | .v128_load8_lane => ⟨[address, .v128], [.v128]⟩
  | .v128_load16_lane => ⟨[address, .v128], [.v128]⟩
  | .v128_load32_lane => ⟨[address, .v128], [.v128]⟩
  | .v128_load64_lane => ⟨[address, .v128], [.v128]⟩
  | .v128_store8_lane => ⟨[address, .v128], []⟩
  | .v128_store16_lane => ⟨[address, .v128], []⟩
  | .v128_store32_lane => ⟨[address, .v128], []⟩
  | .v128_store64_lane => ⟨[address, .v128], []⟩
  | .v128_load32_zero => ⟨[address], [.v128]⟩
  | .v128_load64_zero => ⟨[address], [.v128]⟩
  | .f32x4_demote_f64x2_zero => ⟨[.v128], [.v128]⟩
  | .f64x2_promote_low_f32x4 => ⟨[.v128], [.v128]⟩
  | .i8x16_abs => ⟨[.v128], [.v128]⟩
  | .i8x16_neg => ⟨[.v128], [.v128]⟩
  | .i8x16_popcnt => ⟨[.v128], [.v128]⟩
  | .i8x16_all_true => ⟨[.v128], [.i32]⟩
  | .i8x16_bitmask => ⟨[.v128], [.i32]⟩
  | .i8x16_narrow_i16x8_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_narrow_i16x8_u => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_ceil => ⟨[.v128], [.v128]⟩
  | .f32x4_floor => ⟨[.v128], [.v128]⟩
  | .f32x4_trunc => ⟨[.v128], [.v128]⟩
  | .f32x4_nearest => ⟨[.v128], [.v128]⟩
  | .i8x16_shl => ⟨[.v128, .i32], [.v128]⟩
  | .i8x16_shr_s => ⟨[.v128, .i32], [.v128]⟩
  | .i8x16_shr_u => ⟨[.v128, .i32], [.v128]⟩
  | .i8x16_add => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_add_sat_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_add_sat_u => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_sub => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_sub_sat_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_sub_sat_u => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_ceil => ⟨[.v128], [.v128]⟩
  | .f64x2_floor => ⟨[.v128], [.v128]⟩
  | .i8x16_min_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_min_u => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_max_s => ⟨[.v128, .v128], [.v128]⟩
  | .i8x16_max_u => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_trunc => ⟨[.v128], [.v128]⟩
  | .i8x16_avgr_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extadd_pairwise_i8x16_s => ⟨[.v128], [.v128]⟩
  | .i16x8_extadd_pairwise_i8x16_u => ⟨[.v128], [.v128]⟩
  | .i32x4_extadd_pairwise_i16x8_s => ⟨[.v128], [.v128]⟩
  | .i32x4_extadd_pairwise_i16x8_u => ⟨[.v128], [.v128]⟩
  | .i16x8_abs => ⟨[.v128], [.v128]⟩
  | .i16x8_neg => ⟨[.v128], [.v128]⟩
  | .i16x8_q15mulr_sat_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_all_true => ⟨[.v128], [.i32]⟩
  | .i16x8_bitmask => ⟨[.v128], [.i32]⟩
  | .i16x8_narrow_i32x4_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_narrow_i32x4_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extend_low_i8x16_s => ⟨[.v128], [.v128]⟩
  | .i16x8_extend_high_i8x16_s => ⟨[.v128], [.v128]⟩
  | .i16x8_extend_low_i8x16_u => ⟨[.v128], [.v128]⟩
  | .i16x8_extend_high_i8x16_u => ⟨[.v128], [.v128]⟩
  | .i16x8_shl => ⟨[.v128, .i32], [.v128]⟩
  | .i16x8_shr_s => ⟨[.v128, .i32], [.v128]⟩
  | .i16x8_shr_u => ⟨[.v128, .i32], [.v128]⟩
  | .i16x8_add => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_add_sat_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_add_sat_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_sub => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_sub_sat_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_sub_sat_u => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_nearest => ⟨[.v128], [.v128]⟩
  | .i16x8_mul => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_min_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_min_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_max_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_max_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_avgr_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extmul_low_i8x16_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extmul_high_i8x16_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extmul_low_i8x16_u => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_extmul_high_i8x16_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_abs => ⟨[.v128], [.v128]⟩
  | .i32x4_neg => ⟨[.v128], [.v128]⟩
  | .i32x4_all_true => ⟨[.v128], [.i32]⟩
  | .i32x4_bitmask => ⟨[.v128], [.i32]⟩
  | .i32x4_extend_low_i16x8_s => ⟨[.v128], [.v128]⟩
  | .i32x4_extend_high_i16x8_s => ⟨[.v128], [.v128]⟩
  | .i32x4_extend_low_i16x8_u => ⟨[.v128], [.v128]⟩
  | .i32x4_extend_high_i16x8_u => ⟨[.v128], [.v128]⟩
  | .i32x4_shl => ⟨[.v128, .i32], [.v128]⟩
  | .i32x4_shr_s => ⟨[.v128, .i32], [.v128]⟩
  | .i32x4_shr_u => ⟨[.v128, .i32], [.v128]⟩
  | .i32x4_add => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_sub => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_mul => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_min_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_min_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_max_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_max_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_dot_i16x8_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_extmul_low_i16x8_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_extmul_high_i16x8_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_extmul_low_i16x8_u => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_extmul_high_i16x8_u => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_abs => ⟨[.v128], [.v128]⟩
  | .i64x2_neg => ⟨[.v128], [.v128]⟩
  | .i64x2_all_true => ⟨[.v128], [.i32]⟩
  | .i64x2_bitmask => ⟨[.v128], [.i32]⟩
  | .i64x2_extend_low_i32x4_s => ⟨[.v128], [.v128]⟩
  | .i64x2_extend_high_i32x4_s => ⟨[.v128], [.v128]⟩
  | .i64x2_extend_low_i32x4_u => ⟨[.v128], [.v128]⟩
  | .i64x2_extend_high_i32x4_u => ⟨[.v128], [.v128]⟩
  | .i64x2_shl => ⟨[.v128, .i32], [.v128]⟩
  | .i64x2_shr_s => ⟨[.v128, .i32], [.v128]⟩
  | .i64x2_shr_u => ⟨[.v128, .i32], [.v128]⟩
  | .i64x2_add => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_sub => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_mul => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_eq => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_ne => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_lt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_gt_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_le_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_ge_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_extmul_low_i32x4_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_extmul_high_i32x4_s => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_extmul_low_i32x4_u => ⟨[.v128, .v128], [.v128]⟩
  | .i64x2_extmul_high_i32x4_u => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_abs => ⟨[.v128], [.v128]⟩
  | .f32x4_neg => ⟨[.v128], [.v128]⟩
  | .f32x4_sqrt => ⟨[.v128], [.v128]⟩
  | .f32x4_add => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_sub => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_mul => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_div => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_min => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_max => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_pmin => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_pmax => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_abs => ⟨[.v128], [.v128]⟩
  | .f64x2_neg => ⟨[.v128], [.v128]⟩
  | .f64x2_sqrt => ⟨[.v128], [.v128]⟩
  | .f64x2_add => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_sub => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_mul => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_div => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_min => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_max => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_pmin => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_pmax => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_trunc_sat_f32x4_s => ⟨[.v128], [.v128]⟩
  | .i32x4_trunc_sat_f32x4_u => ⟨[.v128], [.v128]⟩
  | .f32x4_convert_i32x4_s => ⟨[.v128], [.v128]⟩
  | .f32x4_convert_i32x4_u => ⟨[.v128], [.v128]⟩
  | .i32x4_trunc_sat_f64x2_s_zero => ⟨[.v128], [.v128]⟩
  | .i32x4_trunc_sat_f64x2_u_zero => ⟨[.v128], [.v128]⟩
  | .f64x2_convert_low_i32x4_s => ⟨[.v128], [.v128]⟩
  | .f64x2_convert_low_i32x4_u => ⟨[.v128], [.v128]⟩
  | .i8x16_relaxed_swizzle => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_relaxed_trunc_f32x4_s => ⟨[.v128], [.v128]⟩
  | .i32x4_relaxed_trunc_f32x4_u => ⟨[.v128], [.v128]⟩
  | .i32x4_relaxed_trunc_f64x2_s => ⟨[.v128], [.v128]⟩
  | .i32x4_relaxed_trunc_f64x2_u => ⟨[.v128], [.v128]⟩
  | .f32x4_relaxed_madd => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .f32x4_relaxed_nmadd => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .f64x2_relaxed_madd => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .f64x2_relaxed_nmadd => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .i8x16_relaxed_laneselect => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .i16x8_relaxed_laneselect => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .i32x4_relaxed_laneselect => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .i64x2_relaxed_laneselect => ⟨[.v128, .v128, .v128], [.v128]⟩
  | .f32x4_relaxed_min => ⟨[.v128, .v128], [.v128]⟩
  | .f32x4_relaxed_max => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_relaxed_min => ⟨[.v128, .v128], [.v128]⟩
  | .f64x2_relaxed_max => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_relaxed_q15mulr_s => ⟨[.v128, .v128], [.v128]⟩
  | .i16x8_relaxed_dot_i8x16_i7x16_s => ⟨[.v128, .v128], [.v128]⟩
  | .i32x4_relaxed_dot_i8x16_i7x16_add_s => ⟨[.v128, .v128, .v128], [.v128]⟩

def VectorOpcode.isMemory (op : VectorOpcode) : Bool :=
  op.name.startsWith "v128.load" || op.name.startsWith "v128.store"

def VectorOpcode.laneWidth (op : VectorOpcode) : Nat :=
  let shape := (op.name.splitOn ".").head!.toList
  (String.ofList ((shape.drop 1).takeWhile Char.isDigit)).toNat?.getD 128

def VectorOpcode.memoryBytes (op : VectorOpcode) : Nat :=
  let suffix := ((op.name.splitOn ".").drop 1).head!
  if suffix == "load" || suffix == "store" then 16
  else if suffix.contains 'x' then 8
  else
    let digits := (suffix.toList.dropWhile (!Char.isDigit ·)).takeWhile Char.isDigit
    (String.ofList digits).toNat?.getD 128 / 8

def VectorOpcode.laneBound (op : VectorOpcode) : Nat :=
  if op.isMemory then 16 / op.memoryBytes else 128 / op.laneWidth

def VectorOp.ImmediatesValid (op : VectorOp) : Prop :=
  op.opcode ≠ .v128_const ∧
  if op.opcode = .i8x16_shuffle then op.lanes.length = 16 ∧ ∀ x ∈ op.lanes, x < 32
  else if op.opcode.name.endsWith "lane" ||
      (op.opcode.name.splitOn "extract_lane").length > 1 then
    op.lanes.length = 1 ∧ ∀ lane ∈ op.lanes, lane < op.opcode.laneBound
  else op.lanes = []

instance (op : VectorOp) : Decidable op.ImmediatesValid := by
  unfold VectorOp.ImmediatesValid
  infer_instance

inductive VectorInstrTyping (mems : List MemoryType) :
    VectorOp → List ValType → List ValType → Prop where
  | pure (hm : op.opcode.isMemory = false) (hi : op.ImmediatesValid) :
      VectorInstrTyping mems op op.opcode.signature.params op.opcode.signature.results
  | memory (hm : mems[op.memory]? = some memory) (hv : op.opcode.isMemory = true)
      (hi : op.ImmediatesValid) (ha : op.arg.Valid memory.addrType op.opcode.memoryBytes) :
      VectorInstrTyping mems op (op.opcode.signature memory.addrType).params
        (op.opcode.signature memory.addrType).results

def vectorSignature? (mems : List MemoryType) (op : VectorOp) : Option FuncType := do
  if op.ImmediatesValid then
    if op.opcode.isMemory then
      let memory ← mems[op.memory]?
      if op.arg.Valid memory.addrType op.opcode.memoryBytes then
        some (op.opcode.signature memory.addrType)
      else none
    else some op.opcode.signature
  else none

theorem vectorSignature?_sound (h : vectorSignature? mems op = some ft) :
    VectorInstrTyping mems op ft.params ft.results := by
  simp only [vectorSignature?] at h
  split at h
  · split at h
    · cases hm : mems[op.memory]? <;> simp [hm, bind, Option.bind] at h
      rcases h with ⟨ha, rfl⟩
      exact .memory hm (by assumption) (by assumption) ha
    · cases h
      exact .pure (by simpa using (by assumption : ¬op.opcode.isMemory = true)) (by assumption)
  · contradiction

end Wasm
