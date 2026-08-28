import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.96 candidate

The radius is the top grid point in the `79730`-error cell,
`(4 * 79730 + 3) / 2^20`.  The fractional score comparison uses the exact
rational sandwich

`(1-r)^128 <= 2^-66 * (19/37) <= 2^(-66.96)`.

No counting or geometric premise occurs in this module.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6630Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6630 : ℝ≥0 := claimedRadius 319075 1048576
def errors6630 : ℕ := 79768
def score6630 : ℕ := 6700

theorem radius_numerator_exact : 319075 = 4 * errors6630 + 3 := by
  norm_num [errors6630]

theorem radius6630_floor :
    ⌊(radius6630 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6630 := by
  norm_num [radius6630, claimedRadius, errors6630, IRSProfile.Index]

theorem radius6630_cell_cross :
    319075 * Fintype.card IRSProfile.Index <
      (errors6630 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_gap :
    131071 < Fintype.card IRSProfile.Index - errors6630 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_admissible :
    radius6630 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6630, claimedRadius, IRSProfile.minRelativeDistance]

theorem radius6630_score :
    (1 - radius6630) ^ IRSProfile.repetitions ≤ claimedError score6630 := by
  rw [show claimedError score6630 = (1 : ℝ≥0) / 2 ^ (67 : ℕ) by
    unfold claimedError score6630
    norm_num [NNReal.rpow_neg, NNReal.rpow_natCast]]
  rw [← NNReal.coe_le_coe]
  norm_num [radius6630, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

end

end ProximityPrize.SubmissionLower.ContactScore6630Research
