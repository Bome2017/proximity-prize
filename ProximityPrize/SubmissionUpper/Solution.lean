/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.IRSHalfRadius
import ProximityPrize.SubmissionUpper.BelowHalf

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_130048_eq :
    claimedUnsafeRadius 130048 = (127 / 256 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12657 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 130048) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_130048_eq]
  have ht : IRSProfile.repetitions = 128 := rfl
  rw [ht]
  have hcross : (1 : ℝ≥0) - 127 / 256 = 129 / 256 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [hcross]
  have hbits : -(((12657 : Nat) : ℝ) / 100) = -(12657 / 100 : ℝ) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change ((2 : Real) ^ (12657 / 100 : Real))⁻¹ ≤
    (129 / 256 : Real) ^ 128
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (100 : Nat) ≠ 0)]
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [← pow_mul]
  norm_num only [Nat.cast_ofNat, div_mul_cancel₀, OfNat.ofNat, Nat.reduceMul]
  have hbern : (1 : Real) + 2 * (1 / 128) ≤
      (1 + 1 / 128 : Real) ^ 2 :=
    one_add_mul_le_pow (by norm_num : (-2 : Real) ≤ 1 / 128) 2
  have hratio : (2 : Real) ^ 143 ≤ (129 / 128 : Real) ^ 12800 := by
    have hpow : (2 : Real) ^ 143 ≤ (65 / 64 : Real) ^ 6400 := by
      set_option exponentiation.threshold 7000 in
        norm_num
    have hstep : (65 / 64 : Real) ^ 6400 ≤
        ((129 / 128 : Real) ^ 2) ^ 6400 := by
      apply pow_le_pow_left₀ (by positivity)
      norm_num at hbern ⊢
    calc
      (2 : Real) ^ 143 ≤ (65 / 64 : Real) ^ 6400 := hpow
      _ ≤ ((129 / 128 : Real) ^ 2) ^ 6400 := hstep
      _ = (129 / 128 : Real) ^ 12800 := by
        rw [← pow_mul]
  have hfactor : (129 / 256 : Real) =
      (1 / 2 : Real) * (129 / 128 : Real) := by norm_num
  rw [hfactor, mul_pow]
  calc
    ((2 : Real) ^ (12657 : Real))⁻¹ = (1 / 2 : Real) ^ 12657 := by
      rw [div_pow]
      simp
    _ = (1 / 2 : Real) ^ 12800 * (2 : Real) ^ 143 := by
      rw [show 12800 = 12657 + 143 by norm_num, pow_add]
      ring
    _ ≤ (1 / 2 : Real) ^ 12800 * (129 / 128 : Real) ^ 12800 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)

/-- A 1024-coefficient Vieta signature lowers the verified attack bound. -/
theorem candidate : ProtocolClaimUpper 12657 130048 where
  admissible := by
    rw [claimedUnsafeRadius_130048_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hleft : ProximityGap.gridPt (ι := IRSProfile.Index) 130048 ≤ δ := by
      exact hδ.1
    have hsound : winningSetDensity IRSProfile.encoder δ = 1 :=
      ProximityPrize.SubmissionUpper.BelowHalf.IRSProfile.winningSetSoundness_eq_one_suffix
        δ (And.intro hleft hδ.2)
    rw [hsound]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
