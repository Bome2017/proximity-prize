/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.MultiAnchorAttack
import ProximityPrize.SubmissionUpper.PrescribedTop

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

set_option maxRecDepth 100000

theorem claimedUnsafeRadius_122369_eq :
    claimedUnsafeRadius 122369 = (122369 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem two_rpow_eighty_seven_div_hundred_le_one_hundred_seventeen_div_sixty_four :
    (2 : ℝ≥0) ^ ((87 : ℝ) / 100) ≤ 117 / 64 := by
  have hroot :
      ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ 117 / 64 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((87 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ 117 / 64 := hroot

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11613 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122369) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122369_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 122369 / 262144 = 139775 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((11613 : Nat) : ℝ) / 100) =
      (87 : ℝ) / 100 + (-(117 : ℝ)) := by
    norm_num
  rw [hbits, NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
  rw [show (139775 : ℝ≥0) / 262144 =
      (139775 / 131072) * (1 / 2) by ring, mul_pow]
  have hhalf : ((1 : ℝ≥0) / 2) ^ (128 : Nat) =
      (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [NNReal.rpow_neg]
    simp
  rw [hhalf]
  have hshift : (2 : ℝ≥0) ^ (-(117 : ℝ)) =
      (2 : ℝ≥0) ^ (11 : Nat) * (2 : ℝ≥0) ^ (-(128 : ℝ)) := by
    rw [← NNReal.rpow_natCast,
      ← NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
    norm_num
  rw [hshift, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    (2 : ℝ≥0) ^ ((87 : ℝ) / 100) * (2 : ℝ≥0) ^ (11 : Nat) ≤
        (117 / 64) * (2 : ℝ≥0) ^ (11 : Nat) := by
      exact mul_le_mul_of_nonneg_right
        two_rpow_eighty_seven_div_hundred_le_one_hundred_seventeen_div_sixty_four
        (by positivity)
    _ ≤ ((139775 : ℝ≥0) / 131072) ^ (128 : Nat) := by
      norm_num [div_pow, le_div_iff₀, div_le_iff₀]

theorem candidate : ProtocolClaimUpper 11613 122369 where
  admissible := by
    rw [claimedUnsafeRadius_122369_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    by_cases hbridge : δ < ProximityGap.gridPt
        (ι := IRSProfile.Index)
        ProximityPrize.SubmissionUpper.MultiAnchor.bridgeIndex
    · exact ProximityPrize.SubmissionUpper.MultiAnchor.IRSProfile.winningSetDensity_gt_epsilonStar
        δ hδ.1 hbridge
    · have hlower : (61321 / 131072 : ℝ≥0) ≤ δ := by
        simpa [ProximityGap.gridPt,
          ProximityPrize.SubmissionUpper.MultiAnchor.bridgeIndex,
          IRSProfile.Index] using (le_of_not_gt hbridge)
      exact ProximityPrize.SubmissionUpper.PrescribedTop.winningSetDensity_gt_target
        δ hlower hδ.2
  score := candidate_score

end ProximityPrize.Benchmark.Upper
