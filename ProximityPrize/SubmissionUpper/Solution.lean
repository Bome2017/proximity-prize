/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_130048_eq_127_div_256 :
    claimedUnsafeRadius 130048 = (127 / 256 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12700 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 130048) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_130048_eq_127_div_256]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 127 / 256 = 129 / 256 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((12700 : Nat) : ℝ) / 100) =
      (1 : ℝ) + (-(128 : ℝ)) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show (129 : ℝ) / 256 = (129 / 128) * (1 / 2) by ring]
  rw [mul_pow]
  rw [show ((1 : ℝ) / 2) ^ 128 = 2 ^ (-(128 : ℝ)) by
    rw [Real.rpow_neg (by norm_num),
      show (128 : ℝ) = ((128 : Nat) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [Real.rpow_one]
  have hbern := one_add_mul_le_pow (a := (1 / 128 : ℝ)) (by norm_num) 128
  norm_num at hbern ⊢

/-- A 1,024-coefficient fiber collision gives a `127.00`-bit upper bound. -/
theorem candidate : ProtocolClaimUpper 12700 130048 where
  admissible := by
    rw [claimedUnsafeRadius_130048_eq_127_div_256]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (claimedUnsafeRadius 130048)
        IRSProfile.minRelativeDistance := hδ
    rw [ProximityPrize.SubmissionUpper.SubHalfPigeonhole.IRSProfile.winningSetSoundness_eq_one
      δ hband]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
