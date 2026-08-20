/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_129681_eq :
    claimedUnsafeRadius 129681 = (129681 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem two_rpow_seven_fourths_le :
    (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 7 / 2 := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (7 / 4 : ℝ))
    (by norm_num : 0 ≤ (7 / 2 : ℝ)) (by norm_num : (4 : ℕ) ≠ 0)).mp
  calc
    ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ 4 =
        ((2 : ℝ) ^ (7 / 4 : ℝ)) ^ (4 : ℝ) := by
      exact (Real.rpow_natCast ((2 : ℝ) ^ (7 / 4 : ℝ)) 4).symm
    _ = (2 : ℝ) ^ ((7 / 4 : ℝ) * 4) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ 7 := by norm_num
    _ ≤ (7 / 2 : ℝ) ^ 4 := by norm_num

theorem seven_halves_le_ratio_pow :
    (7 / 2 : ℝ) ≤ ((132463 : ℝ) / 131072) ^ 128 := by
  have hblock := one_add_mul_le_pow (a := (1391 / 131072 : ℝ))
    (by norm_num) 16
  have hpow := pow_le_pow_left₀
    (by positivity : 0 ≤ (1 : ℝ) + 16 * (1391 / 131072 : ℝ)) hblock 8
  calc
    (7 / 2 : ℝ) ≤ (1 + 16 * (1391 / 131072 : ℝ)) ^ 8 := by norm_num
    _ ≤ ((1 + (1391 / 131072 : ℝ)) ^ 16) ^ 8 := hpow
    _ = (1 + (1391 / 131072 : ℝ)) ^ 128 := by rw [← pow_mul]
    _ = ((132463 : ℝ) / 131072) ^ 128 := by congr 1 <;> norm_num

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12625 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 129681) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_129681_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 129681 / 262144 = 132463 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((12625 : Nat) : ℝ) / 100) =
      (7 / 4 : ℝ) + (-(128 : ℝ)) := by norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show (132463 : ℝ) / 262144 =
      ((132463 : ℝ) / 131072) * (1 / 2) by ring]
  rw [mul_pow]
  rw [show ((1 : ℝ) / 2) ^ 128 = 2 ^ (-(128 : ℝ)) by
    rw [Real.rpow_neg (by norm_num),
      show (128 : ℝ) = ((128 : Nat) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact two_rpow_seven_fourths_le.trans seven_halves_le_ratio_pow

/-- A 1,391-coefficient fiber collision gives a `126.25`-bit upper bound. -/
theorem candidate : ProtocolClaimUpper 12625 129681 where
  admissible := by
    rw [claimedUnsafeRadius_129681_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (claimedUnsafeRadius 129681)
        IRSProfile.minRelativeDistance := hδ
    rw [ProximityPrize.SubmissionUpper.SubHalfPigeonhole.IRSProfile.winningSetSoundness_eq_one
      δ hband]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
