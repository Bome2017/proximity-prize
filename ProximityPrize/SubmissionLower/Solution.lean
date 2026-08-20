/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower

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

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open scoped NNReal

set_option maxRecDepth 100000

/-- The exact lower baseline consumed by Comparator. -/
theorem candidate : ProtocolClaim 5300 1 4 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError IRSProfile.code (1 / 4 : ℝ≥0) ≤
        reductionTarget :=
      ProximityPrize.SubmissionLower.certifiedGammaError_quarter_le_two_pow_neg_160.trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 1 4 = (1 / 4 : ℝ≥0) := by
      norm_num [claimedRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hError : claimedError 5300 = (1 : ℝ≥0) / 2 ^ (53 : ℕ) := by
      unfold claimedError
      rw [show -((((5300 : ℕ) : ℝ) / 100)) = -((53 : ℕ) : ℝ) by norm_num,
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num
    rw [hError, ← NNReal.coe_le_coe]
    norm_num [claimedRadius, IRSProfile.repetitions, div_le_iff₀]

end ProximityPrize.Benchmark
