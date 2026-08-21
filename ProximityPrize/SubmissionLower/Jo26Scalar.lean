import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

/-- Jo26 profile transfer: affine-line MCA is exactly invariant under the
nonempty IRS row interleaving, at every radius strictly between zero and one. -/
theorem irs_mcaError_eq_base_mcaError (δ : ℝ≥0)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (δ : ℝ) =
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (δ : ℝ) := by
  simpa [IRSProfile.code, IRSProfile.baseCode,
    ReedSolomon.Interleaved.irsCode,
    IRSProfile.totalDimension_div_interleaving] using
    (ProximityGap.mcaError_interleaved_eq IRSProfile.baseCode
      IRSProfile.interleaving δ
      (by norm_num [IRSProfile.interleaving]) hδ_pos hδ_lt)

end ProximityPrize.SubmissionLower
