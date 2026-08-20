/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PrescribedTop

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

-- After clearing denominators and raising to the hundredth power,
-- `2^-116.49 <= (69751/131072)^128` becomes this closed Nat inequality.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 205951 ≤ 69751 ^ 12800 := by decide

theorem claimedUnsafeRadius_122642_eq :
    claimedUnsafeRadius 122642 = (61321 / 131072 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem score_base :
    ((2 : ℝ≥0) ^ (11649 : ℕ))⁻¹ ≤ ((69751 : ℝ≥0) / 131072) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 217600 ≤ 2 ^ 11649 * 69751 ^ 12800 := by
    calc
      (2 : ℕ) ^ 217600 = 2 ^ 11649 * 2 ^ 205951 := by rw [← pow_add]
      _ ≤ 2 ^ 11649 * 69751 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((131072 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (217600 : ℕ) := by
    rw [show (131072 : ℝ≥0) = 2 ^ (17 : ℕ) by norm_num, ← pow_mul]
  have hR : ((131072 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (69751 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11649 : ℕ) := by
    rw [h1]
    have hcast : ((2 : ℕ) ^ 217600 : ℝ≥0) ≤
        ((2 ^ 11649 * 69751 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at hcast
    calc
      (2 : ℝ≥0) ^ (217600 : ℕ) ≤
          2 ^ (11649 : ℕ) * 69751 ^ (12800 : ℕ) := hcast
      _ = (69751 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11649 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11649 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122642) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122642_eq]
  have hcross : (1 : ℝ≥0) - 61321 / 131072 = 69751 / 131072 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show IRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((11649 : ℕ) : ℝ)))
      ≤ ((69751 : ℝ≥0) / 131072) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((11649 : ℕ) : ℝ))) * (1 / 100) =
      -(((11649 : Nat) : ℝ) / 100) by push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by
    push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

theorem candidate : ProtocolClaimUpper 11649 122642 where
  admissible := by
    rw [claimedUnsafeRadius_122642_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (61321 / 131072 : ℝ≥0) IRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_122642_eq] using hδ
    simpa only [epsilonStar] using
      ProximityPrize.SubmissionUpper.PrescribedTop.winningSetDensity_gt_target
        δ hband.1 hband.2
  score := candidate_score

end ProximityPrize.Benchmark.Upper
