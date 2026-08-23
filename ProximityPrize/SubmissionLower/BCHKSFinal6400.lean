import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.BCHKSList6400
import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface6399
import ProximityPrize.SubmissionLower.BCHKSUniversalPolynomialAlignment6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

lemma mca_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (bchksRadius6400 : ℝ) ≤
      (bchksNumerator6400 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6400 : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving bchksRadius6400
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [bchksRadius6400])
          (by norm_num [bchksRadius6400]))
    _ ≤ ENNReal.ofReal ((bchksNumerator6400 : ℝ) /
          Fintype.card IRSProfile.Field) :=
      base_mca_bchks6400_le_of_alignment halign
    _ = (bchksNumerator6400 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

lemma bchks6400_nat_div_le_inv_pow {m q t : ℕ}
    (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by push_cast; ring
  calc (m : ENNReal) / (q : ENNReal) ≤ (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) := ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

theorem certifiedGammaError_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    certifiedGammaError IRSProfile.code bchksRadius6400 ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat : (Code.Lambda BCHKS6400SquaredCode (bchksRadius6400 : ℝ)).toNat ≤ bchksListBound6400 := ENat.toNat_le_of_le_coe bchks6400_lambda_le
  have hList : ((Code.Lambda BCHKS6400SquaredCode (bchksRadius6400 : ℝ)).toNat : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤ (bchksListBound6400 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (bchksRadius6400 : ℝ) + ((Code.Lambda ((IRSProfile.code ^⋈ (Fin 2) : ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) : Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) (bchksRadius6400 : ℝ)).toNat : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤ (bchksNumerator6400 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) + (bchksListBound6400 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by apply add_le_add (mca_bchks6400_le_of_alignment halign); simpa [BCHKS6400SquaredCode] using hList
    _ = ((bchksNumerator6400 + bchksListBound6400 : ℕ) : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by rw [← ENNReal.add_div]; norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by apply bchks6400_nat_div_le_inv_pow; norm_num [bchksNumerator6400, bchksListBound6400]; native_decide

theorem protocolClaim6400_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    ProtocolClaim 6400 307121 1048576 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ProximityPrize.Benchmark.claimedRadius bchksRadius6400 IRSProfile.minRelativeDistance
    norm_num
  · have hle : certifiedGammaError IRSProfile.totalDimension IRSProfile.interleaving IRSProfile.domain (claimedRadius 307121 1048576) ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
      have : claimedRadius 307121 1048576 = bchksRadius6400 := by unfold claimedRadius bchksRadius6400; norm_num
      rw [this]
      have hcert : certifiedGammaError IRSProfile.code bchksRadius6400 ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := certifiedGammaError_bchks6400_le_of_alignment halign
      simpa [IRSProfile.parameters, IRSProfile.code] using hcert
    calc certifiedGammaError IRSProfile.totalDimension IRSProfile.interleaving IRSProfile.domain (claimedRadius 307121 1048576) ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := hle
      _ = (ProximityGap.prizeThreshold : ℝ≥0) := by
          have : (ProximityGap.prizeThreshold : ℝ≥0) = (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
            simp [ProximityGap.prizeThreshold, ToyProblem.ProximityGap.prizeThreshold]
            norm_num
          rw [this]
  · have hsc : (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤ claimedError 6400 := bchks6400_score
    have heq : claimedRadius 307121 1048576 = bchksRadius6400 := by unfold claimedRadius bchksRadius6400; norm_num
    rw [heq]
    exact hsc

end ProximityPrize.SubmissionLower
