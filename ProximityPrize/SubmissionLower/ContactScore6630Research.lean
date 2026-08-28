import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.42 candidate

The radius is the top grid point in the `79194`-error cell,
`(4 * 79194 + 3) / 2^20`. The fractional score comparison uses the exact
rational sandwich

`(1-r)^128 <= 2^-66 * (59/79) <= 2^(-66.42)`.

No counting or geometric premise occurs in this module.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6630Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6630 : ℝ≥0 := claimedRadius 316779 1048576
def errors6630 : ℕ := 79194
def score6630 : ℕ := 6642

theorem radius_numerator_exact : 316779 = 4 * errors6630 + 3 := by
  norm_num [errors6630]

theorem radius6630_floor :
    ⌊(radius6630 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6630 := by
  norm_num [radius6630, claimedRadius, errors6630, IRSProfile.Index]

theorem radius6630_cell_cross :
    316779 * Fintype.card IRSProfile.Index <
      (errors6630 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_gap :
    131071 < Fintype.card IRSProfile.Index - errors6630 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_admissible :
    radius6630 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6630, claimedRadius, IRSProfile.minRelativeDistance]

/-- A low-cost exact rational upper approximation.  The intermediate
exponent `8/19` is just above `42/100`, so the root certificate needs only
a nineteenth-power comparison. -/
theorem two_rpow_42_hundredths_le :
    (2 : ℝ≥0) ^ ((42 : ℝ) / 100) ≤ (79 : ℝ≥0) / 59 := by
  have hroot :
      ((2 : ℝ≥0) ^ (8 : ℕ)) ^ ((19 : ℝ)⁻¹) ≤
        (79 : ℝ≥0) / 59 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 19)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((42 : ℝ) / 100) ≤
        (2 : ℝ≥0) ^ ((8 : ℝ) / 19) := by
      exact NNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = ((2 : ℝ≥0) ^ (8 : ℕ)) ^ ((19 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (79 : ℝ≥0) / 59 := hroot

/-- Exact 128th-power rational comparison at the claimed radius. -/
theorem radius6630_power_rational_bound :
    (1 - radius6630) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (59 / 79) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6630, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6630_score :
    (1 - radius6630) ^ IRSProfile.repetitions ≤ claimedError score6630 := by
  have hscale :
      (59 : ℝ≥0) / 79 ≤ (2 : ℝ≥0) ^ (-((42 : ℝ) / 100)) := by
    calc
      (59 : ℝ≥0) / 79 = 1 / ((79 : ℝ≥0) / 59) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((42 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_42_hundredths_le
      _ = (2 : ℝ≥0) ^ (-((42 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6630) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (59 / 79) :=
      radius6630_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((42 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6630 := by
      unfold claimedError score6630
      rw [show -((((6642 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((42 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6630Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6630Research.radius6630_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6630Research.radius6630_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6630Research.two_rpow_42_hundredths_le
#print axioms ProximityPrize.SubmissionLower.ContactScore6630Research.radius6630_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6630Research.radius6630_score
