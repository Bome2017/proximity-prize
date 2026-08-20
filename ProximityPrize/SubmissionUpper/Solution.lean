/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

set_option maxRecDepth 100000

theorem claimedUnsafeRadius_122692_eq :
    claimedUnsafeRadius 122692 = (30673 / 65536 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11656 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122692) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122692_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  rw [ht]
  have hcross : (1 : ℝ≥0) - 30673 / 65536 = 34863 / 65536 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [hcross]
  have hbits : -(((11656 : Nat) : ℝ) / 100) = -(11656 / 100 : ℝ) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change ((2 : Real) ^ (11656 / 100 : Real))⁻¹ ≤
    (34863 / 65536 : Real) ^ 128
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : Nat) ≠ 0)]
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [← pow_mul]
  norm_num only [Nat.cast_ofNat, div_mul_cancel₀, OfNat.ofNat, Nat.reduceMul]
  have hratio : (2 : Real) ^ 1144 ≤ (34863 / 32768 : Real) ^ 12800 := by
    set_option exponentiation.threshold 13000 in
      norm_num
  have hfactor : (34863 / 65536 : Real) =
      (1 / 2 : Real) * (34863 / 32768 : Real) := by norm_num
  rw [hfactor, mul_pow]
  calc
    ((2 : Real) ^ (11656 : Real))⁻¹ = (1 / 2 : Real) ^ 11656 := by
      rw [div_pow]
      simp
    _ = (1 / 2 : Real) ^ 12800 * (2 : Real) ^ 1144 := by
      rw [show 12800 = 11656 + 1144 by norm_num, pow_add]
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 2 : Real) ^ 12800 * (34863 / 32768 : Real) ^ 12800 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)

theorem candidate : ProtocolClaimUpper 11656 122692 where
  admissible := by
    rw [claimedUnsafeRadius_122692_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    rw [ProximityPrize.SubmissionUpper.SubHalfPigeonhole.IRSProfile.winningSetSoundness_eq_one
      δ hδ]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
