import ProximityPrize.SubmissionLower.Puncture

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal ProbabilityTheory

noncomputable def targetRadius5314 : ℝ≥0 := (262209 : ℝ≥0) / 1048576

lemma targetRadius5314_floor :
    ⌊(targetRadius5314 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 65552 := by
  norm_num [targetRadius5314, IRSProfile.Index]

lemma targetRadius5314_floor_nnreal :
    ⌊targetRadius5314 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = 65552 := by
  norm_num [targetRadius5314, IRSProfile.Index]

lemma exists_target5314_exact_support
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field) (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ)) :
    ∃ support : Finset IRSProfile.Index, support.card = 196592 ∧
      LinearCode.projectedWord
          (fun x => ∑ j, AffineLineGenerator IRSProfile.Field gamma j • rows j x) support ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode support ∧
      ∃ j : Fin 2, LinearCode.projectedWord (rows j) support ∉
        LinearCode.projectedCodeSubmod IRSProfile.baseCode support := by
  apply exists_exact_mca_support_rs
    (domain := IRSProfile.domain) (k := IRSProfile.baseDimension)
    (a := 196592) (by norm_num [IRSProfile.baseDimension]) (by
      norm_num [IRSProfile.baseDimension])
  · intro T hT
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor T
        (show (0 : ℝ) ≤ (targetRadius5314 : ℝ) by positivity)).mp hT
    rw [targetRadius5314_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn] at hcomp
    omega
  · simpa [IRSProfile.baseCode] using hgamma

set_option maxRecDepth 100000 in
lemma target5314_lambda_le_four :
    Code.Lambda ImprovedSquaredCode (targetRadius5314 : ℝ) ≤ (4 : ℕ∞) := by
  apply Code.Lambda_le_of_forall_finset_card_le
  intro y T hT
  by_contra hcard
  push Not at hcard
  have hfive : 5 ≤ T.card := by omega
  obtain ⟨B, hBT, hBcard⟩ :=
    Finset.exists_subset_card_eq (s := T) (n := 5) hfive
  let e : Fin 5 ≃ ↥B := (Finset.equivFinOfCardEq hBcard).symm
  let c : Fin 5 →
      IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field :=
    fun j => (e j).1
  apply no_five_close_words ImprovedSquaredCode y c
  · intro j
    exact (hT (c j) (hBT (e j).2)).1
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  · exact improvedSquaredCode_minDistance
  · norm_num [IRSProfile.Index]
  · intro j
    exact hammingDist_le_of_mem_close
      (hT (c j) (hBT (e j).2)) targetRadius5314_floor_nnreal
  · norm_num

/-- Exact rational lower bound used for the 53.14-bit score certificate. -/
theorem two_rpow_eighty_six_hundred_ge :
    (314 : ℝ≥0) / 173 ≤ (2 : ℝ≥0) ^ ((43 : ℝ) / 50) := by
  have hroot :
      (314 : ℝ≥0) / 173 ≤
        ((2 : ℝ≥0) ^ (43 : ℕ)) ^ ((50 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 50)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (314 : ℝ≥0) / 173 ≤
        ((2 : ℝ≥0) ^ (43 : ℕ)) ^ ((50 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((43 : ℝ) / 50) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

theorem target5314_score_bound :
    (1 - targetRadius5314) ^ IRSProfile.repetitions ≤ claimedError 5314 := by
  calc
    (1 - targetRadius5314) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) * (314 / 173) := by
      rw [← NNReal.coe_le_coe]
      norm_num [targetRadius5314, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) *
          (2 : ℝ≥0) ^ ((43 : ℝ) / 50) := by
      exact mul_le_mul_of_nonneg_left two_rpow_eighty_six_hundred_ge (by positivity)
    _ = claimedError 5314 := by
      unfold claimedError
      rw [show -((((5314 : ℕ) : ℝ) / 100)) =
          -((54 : ℕ) : ℝ) + (43 : ℝ) / 50 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

/-- Once the algebraic extraction supplies the `2^57/|F|` MCA estimate, all remaining
finite-field and list-decoding arithmetic closes the fixed `2^-128` reduction target. -/
theorem certifiedGammaError_target5314_le_of_mca
    (hmca :
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (targetRadius5314 : ℝ) ≤
        ((2 ^ 57 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal)) :
    certifiedGammaError IRSProfile.code targetRadius5314 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  have hLambdaNat :
      (Code.Lambda ImprovedSquaredCode (targetRadius5314 : ℝ)).toNat ≤ 4 :=
    ENat.toNat_le_of_le_coe target5314_lambda_le_four
  have hList :
      ((Code.Lambda ImprovedSquaredCode (targetRadius5314 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (targetRadius5314 : ℝ) +
        ((Code.Lambda
          ((IRSProfile.code ^⋈ (Fin 2) :
            ModuleCode IRSProfile.Index IRSProfile.Field
              (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
            Set (IRSProfile.Index →
              Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
          (targetRadius5314 : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      ((2 ^ 57 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      apply add_le_add hmca
      simpa [ImprovedSquaredCode] using hList
    _ = ((2 ^ 57 + 4 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num
      · norm_num [IRSProfile.Field, KoalaBear.Ext6]
    _ = (((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_div (by simp)]
      norm_num

end ProximityPrize.SubmissionLower
