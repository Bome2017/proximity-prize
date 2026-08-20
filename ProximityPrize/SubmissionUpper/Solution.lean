/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

set_option maxRecDepth 100000

theorem claimedUnsafeRadius_123140_eq :
    claimedUnsafeRadius 123140 = (123140 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem two_rpow_seventeen_div_twenty_le_9013_div_5000 :
    (2 : ℝ≥0) ^ ((17 : ℝ) / 20) ≤ 9013 / 5000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (17 : ℕ)) ^ ((20 : ℝ)⁻¹) ≤ 9013 / 5000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 20)]
    norm_num [div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((17 : ℝ) / 20) =
        ((2 : ℝ≥0) ^ (17 : ℕ)) ^ ((20 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ 9013 / 5000 := hroot

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11715 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 123140) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_123140_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 123140 / 262144 = 139004 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((11715 : Nat) : ℝ) / 100) =
      (17 : ℝ) / 20 + (-(118 : ℝ)) := by
    norm_num
  rw [hbits, NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
  rw [show (139004 : ℝ≥0) / 262144 =
      (139004 / 131072) * (1 / 2) by ring, mul_pow]
  have hhalf : ((1 : ℝ≥0) / 2) ^ (128 : Nat) =
      (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [NNReal.rpow_neg]
    simp
  rw [hhalf]
  have hshift : (2 : ℝ≥0) ^ (-(118 : ℝ)) =
      (2 : ℝ≥0) ^ (10 : Nat) * (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [← NNReal.rpow_natCast,
      ← NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
    norm_num
  rw [hshift, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    (2 : ℝ≥0) ^ ((17 : ℝ) / 20) * (2 : ℝ≥0) ^ (10 : Nat) ≤
        (9013 / 5000) * (2 : ℝ≥0) ^ (10 : Nat) := by
      exact mul_le_mul_of_nonneg_right
        two_rpow_seventeen_div_twenty_le_9013_div_5000 (by positivity)
    _ ≤ ((139004 : ℝ≥0) / 131072) ^ (128 : Nat) := by
      norm_num [div_pow, le_div_iff₀, div_le_iff₀]

theorem candidate : ProtocolClaimUpper 11715 123140 where
  admissible := by
    rw [claimedUnsafeRadius_123140_eq]
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
