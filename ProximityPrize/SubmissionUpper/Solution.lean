/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

set_option maxRecDepth 100000

theorem claimedUnsafeRadius_122972_eq :
    claimedUnsafeRadius 122972 = (122972 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11700 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122972) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122972_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 122972 / 262144 = 139172 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((11700 : Nat) : ℝ) / 100) = (-(117 : ℝ)) := by
    norm_num
  rw [hbits]
  rw [show (139172 : ℝ≥0) / 262144 =
      (139172 / 131072) * (1 / 2) by ring, mul_pow]
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
  rw [hshift]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have : (2 : ℝ≥0) ^ (11 : Nat) ≤
      ((139172 : ℝ≥0) / 131072) ^ (128 : Nat) := by
    norm_num [div_pow, le_div_iff₀, div_le_iff₀]
  simpa using this

theorem candidate : ProtocolClaimUpper 11700 122972 where
  admissible := by
    rw [claimedUnsafeRadius_122972_eq]
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
