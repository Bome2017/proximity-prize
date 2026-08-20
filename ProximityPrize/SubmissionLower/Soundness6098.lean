/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Surface6317

/-! # Complete soundness theorem for the 60.98-bit submission -/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

theorem target_reduction_6098 :
    certifiedGammaError IRSProfile.code targetRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  target_reduction_of_badScalarBound Surface6317.targetBadScalarBound

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

set_option maxRecDepth 100000

/-- The submitted claim: radius `9/32`, reduction error at most `2^-128`, and score `60.98`. -/
theorem candidate_6098 : ProtocolClaim 6098 9 32 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have hr : claimedRadius 9 32 = ProximityPrize.SubmissionLower.targetRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.targetRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact ProximityPrize.SubmissionLower.target_reduction_6098.trans (by
      norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := by
    have hr : claimedRadius 9 32 = ProximityPrize.SubmissionLower.targetRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.targetRadius]
    rw [hr]
    exact ProximityPrize.SubmissionLower.target_score_6098

end ProximityPrize.Benchmark
