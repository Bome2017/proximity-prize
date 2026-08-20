/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.IRSHalfRadius
import ProximityPrize.SubmissionUpper.BelowHalf

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_131072_eq_half :
    claimedUnsafeRadius 131072 = (1 / 2 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem claimedUnsafeRadius_131057_eq :
    claimedUnsafeRadius 131057 = (131057 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12798 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 131057) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_131057_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  rw [ht]
  have hcross : (1 : ℝ≥0) - 131057 / 262144 = 131087 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [hcross]
  have hbits : -(((12798 : Nat) : ℝ) / 100) = -(12798 / 100 : ℝ) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change ((2 : Real) ^ (12798 / 100 : Real))⁻¹ ≤
    (131087 / 262144 : Real) ^ 128
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : Nat) ≠ 0)]
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [← pow_mul]
  norm_num only [Nat.cast_ofNat, div_mul_cancel₀, OfNat.ofNat, Nat.reduceMul]
  have hbern : (1 : Real) + 800 * (15 / 131072) ≤
      (1 + 15 / 131072 : Real) ^ 800 :=
    one_add_mul_le_pow (by norm_num : (-2 : Real) ≤ 15 / 131072) 800
  have hratio : (4 : Real) ≤ (131087 / 131072 : Real) ^ 12800 := by
    have hpow : (4 : Real) ≤ (4471 / 4096 : Real) ^ 16 := by norm_num
    have hstep : (4471 / 4096 : Real) ^ 16 ≤
        ((131087 / 131072 : Real) ^ 800) ^ 16 := by
      apply pow_le_pow_left₀ (by positivity)
      norm_num at hbern ⊢
      exact hbern
    calc
      (4 : Real) ≤ (4471 / 4096 : Real) ^ 16 := hpow
      _ ≤ ((131087 / 131072 : Real) ^ 800) ^ 16 := hstep
      _ = (131087 / 131072 : Real) ^ 12800 := by
        rw [← pow_mul]
  have hfactor : (131087 / 262144 : Real) =
      (1 / 2 : Real) * (131087 / 131072 : Real) := by norm_num
  rw [hfactor, mul_pow]
  calc
    ((2 : Real) ^ (12798 : Real))⁻¹ = (1 / 2 : Real) ^ 12798 := by
      rw [div_pow]
      simp
    _ = (1 / 2 : Real) ^ 12800 * 4 := by
      rw [show 12800 = 12798 + 2 by norm_num, pow_add]
      ring
    _ ≤ (1 / 2 : Real) ^ 12800 * (131087 / 131072 : Real) ^ 12800 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)

/-- Fifteen fixed Vieta coefficients move the certified unsafe radius below one-half. -/
theorem candidate : ProtocolClaimUpper 12798 131057 where
  admissible := by
    rw [claimedUnsafeRadius_131057_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hsound : winningSetDensity IRSProfile.encoder δ = 1 := by
      by_cases hhalf : δ < (1 / 2 : ℝ≥0)
      · apply ProximityPrize.SubmissionUpper.BelowHalf.IRSProfile.winningSetSoundness_eq_one_below_half δ
        exact And.intro (by simpa only [claimedUnsafeRadius_131057_eq] using hδ.1) hhalf
      · apply ProximityPrize.SubmissionUpper.IRSHalfRadius.IRSProfile.winningSetSoundness_eq_one δ
        exact And.intro (le_of_not_gt hhalf) hδ.2
    rw [hsound]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
