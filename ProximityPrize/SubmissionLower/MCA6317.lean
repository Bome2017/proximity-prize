/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Numeric6317

/-!
# Cardinality interface for the target BCHKS MCA proof

The algebraic part of the submission proves a uniform cardinality bound for the exceptional
line parameters.  This file converts that integer statement into ArkLib's `mcaError`, then
transfers it from the base Reed--Solomon code to the fixed width-eight interleaving.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

/-- The exact finite exceptional-set statement required from the BCHKS/BCIKS argument. -/
def TargetBadScalarBound : Prop :=
  ∀ U : Fin 2 → (IRSProfile.Index → IRSProfile.Field),
    (Finset.univ.filter (fun γ : IRSProfile.Field =>
      IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
        (targetRadius : ℝ))).card ≤ targetMcaNumerator

/-- A uniform count of exceptional scalars gives the corresponding base-code probability bound. -/
theorem base_mca_target_le_of_badScalarBound (hbad : TargetBadScalarBound) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (targetRadius : ℝ) ≤
      (targetMcaNumerator : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  exact ENNReal.div_le_div_right (by exact_mod_cast hbad U) _

/-- The target count transfers unchanged to the fixed interleaved code. -/
theorem target_mca_le_of_badScalarBound (hbad : TargetBadScalarBound) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (targetRadius : ℝ) ≤
      (targetMcaNumerator : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (targetRadius : ℝ) ≤
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (targetRadius : ℝ) := by
          simpa [IRSProfile.code, IRSProfile.baseCode,
            ReedSolomon.Interleaved.irsCode,
            IRSProfile.totalDimension_div_interleaving] using
            (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
              IRSProfile.interleaving targetRadius
              (by norm_num [IRSProfile.interleaving])
              (by norm_num [targetRadius]) (by norm_num [targetRadius]))
    _ ≤ _ := base_mca_target_le_of_badScalarBound hbad

/-- Once the algebraic count is supplied, the complete `2^-128` reduction follows. -/
theorem target_reduction_of_badScalarBound (hbad : TargetBadScalarBound) :
    certifiedGammaError IRSProfile.code targetRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_target_of_mca (target_mca_le_of_badScalarBound hbad)

end ProximityPrize.SubmissionLower
