import ProximityPrize.SubmissionLower.BCHKSAlignment6399
import ProximityPrize.SubmissionLower.BCHKSSoundness

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable def bchksRadius6399 : ℝ≥0 := (307081 : ℝ≥0) / 1048576
def bchksErrors6399 : Nat := 76770
def bchksListBound6399 : Nat := 27000

lemma bchksRadius6399_floor :
    ⌊(bchksRadius6399 : Real) * (Fintype.card IRSProfile.Index : Real)⌋₊ =
      bchksErrors6399 := by
  norm_num [bchksRadius6399, bchksErrors6399, IRSProfile.Index]

theorem two_rpow_one_hundred_ge :
    (10069 : ℝ≥0) / 10000 ≤ (2 : ℝ≥0) ^ ((1 : Real) / 100) := by
  have hroot : (10069 : ℝ≥0) / 10000 ≤
      ((2 : ℝ≥0) ^ (1 : Nat)) ^ ((100 : Real)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : Real) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (10069 : ℝ≥0) / 10000 ≤
        ((2 : ℝ≥0) ^ (1 : Nat)) ^ ((100 : Real)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((1 : Real) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

lemma bchksRadius6399_score :
    (1 - bchksRadius6399) ^ IRSProfile.repetitions ≤ claimedError 6399 := by
  calc
    (1 - bchksRadius6399) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : Nat)) * (10069 / 10000) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius6399, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : Nat)) *
          (2 : ℝ≥0) ^ ((1 : Real) / 100) := by
      exact mul_le_mul_of_nonneg_left two_rpow_one_hundred_ge (by positivity)
    _ = claimedError 6399 := by
      unfold claimedError
      rw [show -((((6399 : Nat) : Real) / 100)) =
          -((64 : Nat) : Real) + (1 : Real) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

lemma bchks_budget_nat_6399 :
    2 ^ (128 : Nat) * (bchksNumerator + bchksListBound6399) ≤
      (2130706433 : Nat) ^ 6 := by
  norm_num [bchksNumerator, bchksListBound6399]

private lemma bchks_eta_pos_6399 :
    0 < (1 - Real.sqrt (1 / 2 : Real) - (bchksRadius6399 : Real)) := by
  have hs : Real.sqrt (1 / 2 : Real) < 70710679 / 100000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < 70710679 / 100000000)]
    norm_num
  norm_num [bchksRadius6399] at hs ⊢
  linarith

set_option maxRecDepth 100000 in
lemma bchks_lambda_le_6399 :
    Code.Lambda BCHKSSquaredCode (bchksRadius6399 : Real) ≤
      (bchksListBound6399 : ℕ∞) := by
  let η : Real := 1 - Real.sqrt (1 / 2 : Real) - (bchksRadius6399 : Real)
  have hη : 0 < η := by simpa [η] using bchks_eta_pos_6399
  have hJ := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    BCHKSSquaredCode (1 / 2 : Real) η (by norm_num) (by norm_num) hη (by
      rw [bchksSquaredCode_minDistance]
      norm_num [IRSProfile.Index])
  have hr : 1 - Real.sqrt (1 / 2 : Real) - η = (bchksRadius6399 : Real) := by
    simp [η]
  rw [hr] at hJ
  have hreal : (1 / (2 * η * (1 / 2 : Real))) ≤ bchksListBound6399 := by
    dsimp [η, bchksListBound6399]
    have hs : Real.sqrt (1 / 2 : Real) < 70710679 / 100000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < 70710679 / 100000000)]
      norm_num
    have heta : (1 : Real) / 27000 < η := by
      dsimp [η]
      norm_num [bchksRadius6399] at hs ⊢
      linarith
    rw [show 2 * η * (1 / 2 : Real) = η by ring]
    rw [div_le_iff₀ hη]
    nlinarith
  have hE : (Code.Lambda BCHKSSquaredCode (bchksRadius6399 : Real) : ENNReal) ≤
      (bchksListBound6399 : ENNReal) := hJ.trans (by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

theorem base_mca_bchks_le_of_alignment_6399
    (halign : AffineLineAlignmentBound IRSProfile.baseCode 76770 bchksNumerator) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6399 : Real) ≤
      ENNReal.ofReal ((bchksNumerator : Real) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius6399 : Real) 76770 bchksNumerator
  · intro A hA
    have hcomp := (mul_one_sub_le_card_iff_sub_card_le_floor A
      (show (0 : Real) ≤ (bchksRadius6399 : Real) by positivity)).mp hA
    rw [bchksRadius6399_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors6399] at hcomp ⊢
    omega
  · exact halign

theorem mca_bchks_le_of_alignment_6399
    (halign : AffineLineAlignmentBound IRSProfile.baseCode 76770 bchksNumerator) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (bchksRadius6399 : Real) ≤
      (bchksNumerator : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6399 : Real) := by
      simpa [IRSProfile.code, IRSProfile.baseCode, ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving bchksRadius6399
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [bchksRadius6399]) (by norm_num [bchksRadius6399]))
    _ ≤ ENNReal.ofReal ((bchksNumerator : Real) / Fintype.card IRSProfile.Field) :=
      base_mca_bchks_le_of_alignment_6399 halign
    _ = (bchksNumerator : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem certifiedGammaError_bchks_le_of_alignment_6399
    (halign : AffineLineAlignmentBound IRSProfile.baseCode 76770 bchksNumerator) :
    certifiedGammaError IRSProfile.code bchksRadius6399 ≤
      (1 : ℝ≥0) / 2 ^ (128 : Nat) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat :
      (Code.Lambda BCHKSSquaredCode (bchksRadius6399 : Real)).toNat ≤
        bchksListBound6399 := ENat.toNat_le_of_le_coe bchks_lambda_le_6399
  have hList :
      ((Code.Lambda BCHKSSquaredCode (bchksRadius6399 : Real)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (bchksListBound6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (bchksRadius6399 : Real) +
        ((Code.Lambda BCHKSSquaredCode (bchksRadius6399 : Real)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      (bchksNumerator : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (bchksListBound6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca_bchks_le_of_alignment_6399 halign) hList
    _ = ((bchksNumerator + bchksListBound6399 : Nat) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : Nat) := by
      apply bchks_nat_div_le_inv_pow
      · norm_num [bchksNumerator, bchksListBound6399]
      · simpa [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize,
          Nat.mul_comm] using bchks_budget_nat_6399

theorem certifiedGammaError_bchks_le_6399 :
    certifiedGammaError IRSProfile.code bchksRadius6399 ≤
      (1 : ℝ≥0) / 2 ^ (128 : Nat) :=
  certifiedGammaError_bchks_le_of_alignment_6399
    (alignmentBound_of_polynomialAlignment_6399 bchksPolynomialAlignment6399)

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

theorem protocolClaim6399 : ProtocolClaim 6399 307081 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.bchksRadius6399 ≤ reductionTarget :=
      ProximityPrize.SubmissionLower.certifiedGammaError_bchks_le_6399 |>.trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 307081 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6399 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6399]
    have hc : ReedSolomon.Interleaved.irsCode IRSProfile.domain
        IRSProfile.totalDimension IRSProfile.interleaving = IRSProfile.code := rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 307081 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6399 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6399]
    rw [hr]
    exact ProximityPrize.SubmissionLower.bchksRadius6399_score

end ProximityPrize.Benchmark
