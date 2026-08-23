import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

noncomputable def bchksRadius6400 : ℝ≥0 := (307121 : ℝ≥0) / 1048576

def bchksErrors6400 : ℕ := 76780
def bchksNumerator6400 : ℕ := 120000000000000000
def bchksListBound6400 : ℕ := 200000
def bchksMultiplicity6400 : ℕ := 3733
def bchksXCap6400 : ℕ := 691963812
def bchksYCap6400 : ℕ := 5280
def bchksZCap6400 : ℕ := 13141403
def bchksFactorMass6400 : ℕ := 5279
def bchksFactorZMass6400 : ℕ := 13141402
def bchksUniversalExponent6400 : ℕ := 262141
def bchksIncidenceCoefficient6400 : ℕ := 1265711

lemma bchksRadius6400_floor :
    ⌊(bchksRadius6400 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

lemma bchksRadius6400_floor_nnreal :
    ⌊bchksRadius6400 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

lemma bchks6400_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator6400, bchksListBound6400]

lemma bchks6400_score :
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6400 := by
  calc
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
        (1 : ℝ≥0) / 2 ^ (64 : ℕ) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius6400, IRSProfile.repetitions, div_le_iff₀]
    _ = ProximityPrize.Benchmark.claimedError 6400 := by
      unfold ProximityPrize.Benchmark.claimedError
      rw [show -((((6400 : ℕ) : ℝ) / 100)) = -((64 : ℕ) : ℝ) by norm_num,
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

lemma bchks6400_universal_seed_budget :
    1265711 * (5280 - 1) * (13141403 - 1) +
      (bchksErrors6400 + 1) * (5280 - 1) +
      2 * 13141403 * (5280 - 1) + 13141403 <
        bchksNumerator6400 := by
  norm_num [bchksErrors6400, bchksNumerator6400]

lemma bchks6400_incidence_rounding :
    (262144 - 131071) * (2 * (2 * 131071 - 1)) ≤
      1265711 * (262144 - bchksErrors6400 - 131071) := by
  norm_num [bchksErrors6400]

lemma bchks6400_resultant_degree_cap :
    2 * bchksUniversalExponent6400 * bchksFactorMass6400 *
        bchksFactorZMass6400 + bchksFactorMass6400 =
      36371256962843835 := by
  norm_num [bchksUniversalExponent6400, bchksFactorMass6400,
    bchksFactorZMass6400]

lemma bchks6400_fused_incidence :
    (262144 - 131071) *
        (2 * bchksUniversalExponent6400 * bchksFactorMass6400 *
          bchksFactorZMass6400 + bchksFactorMass6400) ≤
      (262144 - bchksErrors6400 - 131071) *
        (bchksIncidenceCoefficient6400 * bchksFactorMass6400 *
          bchksFactorZMass6400) := by
  norm_num [bchksUniversalExponent6400, bchksFactorMass6400,
    bchksFactorZMass6400, bchksErrors6400,
    bchksIncidenceCoefficient6400]

lemma bchks6400_gap_pos :
    0 < 262144 - bchksErrors6400 - 131071 := by
  norm_num [bchksErrors6400]

lemma bchks6400_gap_le_nminus :
    262144 - bchksErrors6400 - 131071 ≤ 262144 - 131071 := by
  norm_num [bchksErrors6400]

theorem base_mca_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6400 : ℝ) ≤
      ENNReal.ofReal
        ((bchksNumerator6400 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius6400 : ℝ) bchksErrors6400 bchksNumerator6400
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius6400 : ℝ) by positivity)).mp hA
    rw [bchksRadius6400_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors6400] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionLower
