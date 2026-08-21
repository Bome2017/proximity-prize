import ProximityPrize.SubmissionLower.Puncture

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal

/-- Exact rational lower bound used for the 53.13-bit score certificate. -/
theorem two_rpow_eighty_seven_hundred_ge :
    (731 : ℝ≥0) / 400 ≤ (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
  have hroot :
      (731 : ℝ≥0) / 400 ≤
        ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (731 : ℝ≥0) / 400 ≤
        ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open scoped NNReal

set_option maxRecDepth 100000

/-- Certified 53.13-bit lower bound at a radius in the 65541st Hamming cell. -/
theorem candidate : ProtocolClaim 5313 262167 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have hr : claimedRadius 262167 1048576 =
        ProximityPrize.SubmissionLower.improvedRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.improvedRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    simpa [reductionTarget, ProximityGap.prizeThreshold] using
      ProximityPrize.SubmissionLower.certifiedGammaError_improved_le
  score := by
    calc
      (1 - claimedRadius 262167 1048576) ^ IRSProfile.repetitions ≤
          ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) * (731 / 400) := by
        rw [← NNReal.coe_le_coe]
        norm_num [claimedRadius, IRSProfile.repetitions, div_le_iff₀]
      _ ≤ ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) *
            (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
        exact mul_le_mul_of_nonneg_left
          ProximityPrize.SubmissionLower.two_rpow_eighty_seven_hundred_ge
          (by positivity)
      _ = claimedError 5313 := by
        unfold claimedError
        rw [show -((((5313 : ℕ) : ℝ) / 100)) =
            -((54 : ℕ) : ℝ) + (87 : ℝ) / 100 by norm_num,
          NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
          NNReal.rpow_neg, NNReal.rpow_natCast]
        norm_num

end ProximityPrize.Benchmark
