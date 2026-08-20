/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PostQuarter
import ProximityPrize.SubmissionLower.Puncture

/-!
# Lower reduction-threshold baseline

At radius `1/4`, the certified IRS combination-round error is below `2^-160`.
The separate spot-check term `(3/4)^128` is below `2^-53`, giving the exact
`53.00`-bit baseline required by the lower challenge.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

set_option maxRecDepth 100000

noncomputable abbrev SquaredCode : Set (IRSProfile.Index →
    Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem squaredCode_minDistance :
    Code.minDist (SquaredCode : Set (IRSProfile.Index →
      Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) = 131073 := by
  calc
    Code.minDist (SquaredCode : Set (IRSProfile.Index →
        Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) =
      Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field)) := by
          exact Code.minDist_interleavedCodeSet (κ := Fin 2)
            (IRSProfile.code : Set (IRSProfile.Index →
              Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

theorem squaredCode_relativeUniqueDecodingRadius :
    Code.relativeUniqueDecodingRadius
      (SquaredCode : Set (IRSProfile.Index →
        Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) =
      (1 : ℝ≥0) / 4 := by
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, squaredCode_minDistance]
  apply NNReal.eq
  norm_num

theorem squaredCode_lambda_quarter_le_one :
    Code.Lambda
      (SquaredCode : Set (IRSProfile.Index →
        Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (1 / 4 : ℝ) ≤ 1 := by
  have h := Code.isUniquelyDecodable_relativeUniqueDecodingRadius
    (SquaredCode : Set (IRSProfile.Index →
      Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
  rw [squaredCode_relativeUniqueDecodingRadius] at h
  exact Code.isUniquelyDecodable_iff_Lambda_le.mp h

theorem baseCode_relativeUniqueDecodingRadius :
    Code.relativeUniqueDecodingRadius
      (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field)) =
      (1 : ℝ≥0) / 4 := by
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, IRSProfile.baseMinDistance]
  apply NNReal.eq
  norm_num

theorem base_mca_quarter_le :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (1 / 4 : ℝ) ≤
      (Fintype.card IRSProfile.Index : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  have hudr : (1 / 4 : ℝ≥0) ≤
      Code.relativeUniqueDecodingRadius
        (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field)) := by
    rw [baseCode_relativeUniqueDecodingRadius]
  have hca :=
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime
      (deg := IRSProfile.baseDimension) (domain := IRSProfile.domain)
      (δ := (1 / 4 : ℝ≥0)) hudr
  have heps :=
    (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le
      (F := IRSProfile.Field)
      (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field))
      (1 / 4 : ℝ≥0)
      (ProximityGap.errorBound (1 / 4 : ℝ≥0)
        IRSProfile.baseDimension IRSProfile.domain)).mp hca
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
          (1 / 4 : ℝ) ≤
        epsCa (F := IRSProfile.Field)
          (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field))
          (1 / 4 : ℝ≥0) (1 / 4 : ℝ≥0) := by
      refine ProximityGap.mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
        (ι := IRSProfile.Index) (F := IRSProfile.Field)
        IRSProfile.baseCode (1 / 4 : ℝ≥0) ?_ ?_
      · norm_num
      · rw [Code.dist_eq_minDist, IRSProfile.baseMinDistance]
        norm_num
    _ ≤ (Fintype.card IRSProfile.Index : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ProximityGap.errorBound_eq_n_div_q_of_le_relUDR hudr] at heps
      rw [ENNReal.coe_div (by simp)] at heps
      exact heps

theorem mca_quarter_le :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (1 / 4 : ℝ) ≤
      (Fintype.card IRSProfile.Index : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (1 / 4 : ℝ) ≤
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (1 / 4 : ℝ) := by
          simpa [IRSProfile.code, IRSProfile.baseCode,
            ReedSolomon.Interleaved.irsCode,
            IRSProfile.totalDimension_div_interleaving] using
            (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
              IRSProfile.interleaving (1 / 4 : ℝ≥0)
              (by norm_num [IRSProfile.interleaving]) (by norm_num) (by norm_num))
    _ ≤ _ := base_mca_quarter_le

theorem certifiedGammaError_quarter_le_two_pow_neg_160 :
    certifiedGammaError IRSProfile.code (1 / 4 : ℝ≥0) ≤
      (1 : ℝ≥0) / 2 ^ (160 : ℕ) := by
  have hLambdaNat :
      (Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat ≤ 1 :=
    ENat.toNat_le_of_le_coe squaredCode_lambda_quarter_le_one
  have hList :
      ((Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (1 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
    exact ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (1 / 4 : ℝ) +
          ((Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
        (Fintype.card IRSProfile.Index : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) +
          (1 : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add mca_quarter_le hList
    _ ≤ (((1 : ℝ≥0) / 2 ^ (160 : ℕ) : ℝ≥0) : ENNReal) := by
      have hne :
          (Fintype.card IRSProfile.Index : ENNReal) /
                (Fintype.card IRSProfile.Field : ENNReal) +
              1 / (Fintype.card IRSProfile.Field : ENNReal) ≠ ⊤ := by
        rw [ENNReal.add_ne_top]
        constructor <;> apply ENNReal.div_ne_top <;> simp
      apply (ENNReal.toReal_le_toReal hne (by simp)).mp
      have hparts := ENNReal.add_ne_top.mp hne
      rw [ENNReal.toReal_add hparts.1 hparts.2,
        ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num [IRSProfile.Index, IRSProfile.Field, KoalaBear.Ext6]

theorem two_rpow_twenty_two_div_twenty_five_ge :
    (235 : ℝ≥0) / 128 ≤ (2 : ℝ≥0) ^ ((22 : ℝ) / 25) := by
  have hroot :
      (235 : ℝ≥0) / 128 ≤
        ((2 : ℝ≥0) ^ (22 : ℕ)) ^ ((25 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 25)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (235 : ℝ≥0) / 128 ≤
        ((2 : ℝ≥0) ^ (22 : ℕ)) ^ ((25 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((22 : ℝ) / 25) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open scoped NNReal

set_option maxRecDepth 100000

/-- The first certified point beyond the unique-decoding quarter radius. -/
theorem candidate : ProtocolClaim 5313 2731 10923 where
  admissible :=
    ProximityPrize.SubmissionLower.improvedRadius_admissible
  reduction := by
    have hmca39 :
        CoreDefinitions.mcaError
            (CoreDefinitions.AffineLineGenerator IRSProfile.Field)
            IRSProfile.baseCode
            (ProximityPrize.SubmissionLower.delta65541 : ℝ) ≤
          (2 : ENNReal) ^ (39 : ℕ) /
            (Fintype.card IRSProfile.Field : ENNReal) := by
      simpa [ProximityPrize.SubmissionLower.delta65541,
        ProximityPrize.SubmissionLower.postQuarterRadius5] using
        ProximityPrize.SubmissionLower.base_mca_postQuarter_le_two_pow_39
    have hmca57 :
        CoreDefinitions.mcaError
            (CoreDefinitions.AffineLineGenerator IRSProfile.Field)
            IRSProfile.baseCode
            (ProximityPrize.SubmissionLower.delta65541 : ℝ) ≤
          (2 : ENNReal) ^ (57 : ℕ) /
            (Fintype.card IRSProfile.Field : ENNReal) := by
      exact hmca39.trans (ENNReal.div_le_div_right (by norm_num) _)
    have hcert :=
      ProximityPrize.SubmissionLower.certifiedGammaError_improvedRadius_le_of_base_mca
        hmca57
    have h : ToyProblem.certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.improvedRadius ≤ reductionTarget :=
      hcert.trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 2731 10923 =
        ProximityPrize.SubmissionLower.improvedRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.improvedRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := ProximityPrize.SubmissionLower.improvedRadius_score_5313

end ProximityPrize.Benchmark
