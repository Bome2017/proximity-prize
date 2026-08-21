import ProximityPrize.SubmissionLower.Target5314FullAlignment
import ProximityPrize.SubmissionLower.AlignmentFromPolynomials
import ProximityPrize.SubmissionLower.MCAFinal5314

namespace ProximityPrize.Benchmark

open scoped NNReal

set_option maxRecDepth 1000000
set_option maxHeartbeats 300000

/-- Certified 53.14-bit lower bound at radius `262209 / 1048576`. -/
theorem candidate : ProtocolClaim 5314 262209 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have halignSelected :=
      ProximityPrize.SubmissionLower.Target5314FullAlignment.hasLargeSelectedPolynomialAlignment5314
    have halign :=
      ProximityPrize.SubmissionLower.largeAffineCollisionAlignment_of_selectedPolynomialAlignment
        halignSelected
    have hcert :=
      ProximityPrize.SubmissionLower.certifiedGammaError_target5314_le_of_alignment
        halign
    have hr : claimedRadius 262209 1048576 =
        ProximityPrize.SubmissionLower.targetRadius5314 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.targetRadius5314]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    simpa [reductionTarget, ProximityGap.prizeThreshold] using hcert
  score := by
    have hr : claimedRadius 262209 1048576 =
        ProximityPrize.SubmissionLower.targetRadius5314 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.targetRadius5314]
    rw [hr]
    exact ProximityPrize.SubmissionLower.target5314_score_bound

end ProximityPrize.Benchmark
