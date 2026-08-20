/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PrescribedTop

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

-- The exact spot-check comparison at `delta* = 122651/262144`, in `Nat`:
-- `2 ^ 218749 <= 139493 ^ 12800` is
-- `2 ^ (-11651/100) <= (139493/262144) ^ 128`
-- after clearing denominators and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 218749 ≤ 139493 ^ 12800 := by decide

theorem claimedUnsafeRadius_122651_eq :
    claimedUnsafeRadius 122651 = (122651 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem score_base :
    ((2 : ℝ≥0) ^ (11651 : ℕ))⁻¹ ≤ ((139493 : ℝ≥0) / 262144) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 230400 ≤ 2 ^ 11651 * 139493 ^ 12800 := by
    calc (2 : ℕ) ^ 230400 = 2 ^ 11651 * 2 ^ 218749 := by rw [← pow_add]
      _ ≤ 2 ^ 11651 * 139493 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((262144 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (230400 : ℕ) := by
    rw [show (262144 : ℝ≥0) = 2 ^ (18 : ℕ) by norm_num, ← pow_mul]
  have hR : ((262144 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (139493 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11651 : ℕ) := by
    rw [h1]
    have : ((2 : ℕ) ^ 230400 : ℝ≥0) ≤ ((2 ^ 11651 * 139493 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at this
    calc (2 : ℝ≥0) ^ (230400 : ℕ) ≤ 2 ^ (11651 : ℕ) * 139493 ^ (12800 : ℕ) := this
      _ = (139493 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11651 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11651 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122651) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122651_eq]
  have hcross : (1 : ℝ≥0) - 122651 / 262144 = 139493 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show IRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((11651 : ℕ) : ℝ)))
      ≤ ((139493 : ℝ≥0) / 262144) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((11651 : ℕ) : ℝ))) * (1 / 100) = -(((11651 : Nat) : ℝ) / 100) by
    push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

/-- The prescribed-top-coefficient collision family certifies the unsafe suffix
from `delta* = 122651/262144` onward, giving a `116.51`-bit upper certificate. -/
theorem candidate : ProtocolClaimUpper 11651 122651 where
  admissible := by
    rw [claimedUnsafeRadius_122651_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (122651 / 262144 : ℝ≥0) IRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_122651_eq] using hδ
    rw [ProximityPrize.SubmissionUpper.PrescribedTop.winningSetDensity_eq_one
      δ hband.1 hband.2]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
