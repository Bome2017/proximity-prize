import ProximityPrize.SubmissionLower.LineDecodingBridge
import ProximityPrize.SubmissionLower.Target5314

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal ProbabilityTheory

lemma base_mca_target5314_le_of_alignment
    (halign : CodingTheory.HasLargeAffineCollisionAlignment
      IRSProfile.baseCode (targetRadius5314 : ℝ) (2 ^ 57)) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (targetRadius5314 : ℝ) ≤
      ((2 ^ 57 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) :=
  halign.mcaError_le IRSProfile.baseCode (targetRadius5314 : ℝ) (2 ^ 57)

lemma irs_mca_target5314_le_of_alignment
    (halign : CodingTheory.HasLargeAffineCollisionAlignment
      IRSProfile.baseCode (targetRadius5314 : ℝ) (2 ^ 57)) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (targetRadius5314 : ℝ) ≤
      ((2 ^ 57 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (targetRadius5314 : ℝ) ≤
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (targetRadius5314 : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving targetRadius5314
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [targetRadius5314]) (by norm_num [targetRadius5314]))
    _ ≤ _ := base_mca_target5314_le_of_alignment halign

theorem certifiedGammaError_target5314_le_of_alignment
    (halign : CodingTheory.HasLargeAffineCollisionAlignment
      IRSProfile.baseCode (targetRadius5314 : ℝ) (2 ^ 57)) :
    certifiedGammaError IRSProfile.code targetRadius5314 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_target5314_le_of_mca
    (irs_mca_target5314_le_of_alignment halign)

end ProximityPrize.SubmissionLower
