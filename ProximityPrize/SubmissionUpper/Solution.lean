/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfBaseField

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

set_option maxRecDepth 100000

theorem claimedUnsafeRadius_122687_eq :
    claimedUnsafeRadius 122687 = (122687 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem two_rpow_split_le :
    (2 : ℝ≥0) ^ ((45 : ℝ) / 100) ≤ 41 / 30 := by
  have hroot :
      ((2 : ℝ≥0) ^ (45 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ 41 / 30 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((45 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (45 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ 41 / 30 := hroot

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11655 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122687) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122687_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 122687 / 262144 = 139457 / 262144 := by
    rw [tsub_eq_of_eq_add]; norm_num
  rw [ht, hcross]
  have hbits : -(((11655 : Nat) : ℝ) / 100) =
      (45 : ℝ) / 100 + (-(117 : ℝ)) := by norm_num
  rw [hbits, NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
  rw [show (139457 : ℝ≥0) / 262144 =
      (139457 / 131072) * (1 / 2) by ring, mul_pow]
  have hhalf : ((1 : ℝ≥0) / 2) ^ (128 : Nat) =
      (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [NNReal.rpow_neg]; simp
  rw [hhalf]
  have hshift : (2 : ℝ≥0) ^ (-(117 : ℝ)) =
      (2 : ℝ≥0) ^ (11 : Nat) * (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [← NNReal.rpow_natCast,
      ← NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
    norm_num
  rw [hshift, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    (2 : ℝ≥0) ^ ((45 : ℝ) / 100) * (2 : ℝ≥0) ^ (11 : Nat) ≤
        (41 / 30) * (2 : ℝ≥0) ^ (11 : Nat) :=
      mul_le_mul_of_nonneg_right two_rpow_split_le (by positivity)
    _ ≤ ((139457 : ℝ≥0) / 131072) ^ (128 : Nat) := by
      norm_num [div_pow, le_div_iff₀, div_le_iff₀]

theorem candidate : ProtocolClaimUpper 11655 122687 where
  admissible := by
    rw [claimedUnsafeRadius_122687_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    rw [ProximityPrize.SubmissionUpper.SubHalfBaseField.IRSProfile.winningSetSoundness_eq_one
      δ hδ]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
