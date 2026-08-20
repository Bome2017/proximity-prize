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

theorem two_pow_69_le_seven_pow_25 : (2 : ℕ) ^ 69 ≤ (7 : ℕ) ^ 25 := by
  have h2 : (7 : ℕ) ^ 2 = 49 := by decide
  have h4 : (7 : ℕ) ^ 4 = 2401 := by
    rw [show (7 : ℕ) ^ 4 = 7 ^ (2 * 2) from rfl, pow_mul, h2]
    decide
  have h5 : (7 : ℕ) ^ 5 = 16807 := by
    rw [show (7 : ℕ) ^ 5 = 7 ^ (4 + 1) from rfl, pow_succ, h4]
    decide
  have h10 : (7 : ℕ) ^ 10 = 282475249 := by
    rw [show (7 : ℕ) ^ 10 = 7 ^ (5 * 2) from rfl, pow_mul, h5]
    decide
  have h20 : (7 : ℕ) ^ 20 = 79792266297612001 := by
    rw [show (7 : ℕ) ^ 20 = 7 ^ (10 * 2) from rfl, pow_mul, h10]
    decide
  have h25 : (7 : ℕ) ^ 25 = 1341068619663964900807 := by
    rw [show (7 : ℕ) ^ 25 = 7 ^ (20 + 5) from rfl, pow_add, h20, h5]
    decide
  have h69 : (2 : ℕ) ^ 69 = 590295810358705651712 := by decide
  rw [h25, h69]
  decide

theorem two_rpow_44_div_25_le_seven_halves :
    (2 : ℝ) ^ ((44 : ℝ) / 25) ≤ 7 / 2 := by
  have h2pos : (0 : ℝ) ≤ 2 := by norm_num
  have hstep :
      ((2 : ℝ) ^ ((44 : ℝ) / 25)) ^ (25 : ℕ) ≤ (7 / 2 : ℝ) ^ (25 : ℕ) := by
    have hmul : ((44 : ℝ) / 25) * (25 : ℝ) = 44 := by norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2pos]
    rw [show ((25 : ℕ) : ℝ) = (25 : ℝ) from rfl, hmul]
    rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (25 : ℕ) := by positivity
    rw [div_pow, le_div_iff₀ hpos, ← pow_add]
    have hadd : 44 + 25 = 69 := by decide
    rw [hadd]
    exact_mod_cast two_pow_69_le_seven_pow_25
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by decide : (25 : ℕ) ≠ 0)).mp hstep

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12624 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 129681) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_129681_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 129681 / 262144 = 132463 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((12624 : Nat) : ℝ) / 100) =
      ((44 : ℝ) / 25) + (-(128 : ℝ)) := by norm_num
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
  exact two_rpow_44_div_25_le_seven_halves.trans seven_halves_le_ratio_pow

/-- Same 1,391-coefficient fiber collision as the 126.25 certificate;
`2^{1.76} ≤ 7/2` via `2^69 ≤ 7^25` tightens the score by one centibit. -/
theorem candidate : ProtocolClaimUpper 12624 129681 where
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
