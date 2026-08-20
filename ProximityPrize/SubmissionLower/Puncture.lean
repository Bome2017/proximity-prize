/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower

/-!
# Finite puncturing at the first post-unique-decoding cell

This file develops the restriction and counting lemmas used to charge the five
post-quarter error shells to shorter Reed--Solomon codes that are again in the
unique-decoding regime.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal BigOperators ProbabilityTheory

noncomputable section

abbrev PuncturedIndex (J : Finset IRSProfile.Index) :=
  {i : IRSProfile.Index // i ∉ J}

def puncturedDomain (J : Finset IRSProfile.Index) :
    PuncturedIndex J ↪ IRSProfile.Field :=
  ⟨fun i => IRSProfile.domain i.1,
    fun _ _ h => Subtype.ext (IRSProfile.domain.injective h)⟩

noncomputable abbrev puncturedCode (J : Finset IRSProfile.Index) :=
  ReedSolomon.code (puncturedDomain J) IRSProfile.baseDimension

noncomputable abbrev puncturedRadius10 : ℝ≥0 :=
  (65531 : ℝ≥0) / 262134

theorem card_puncturedIndex (J : Finset IRSProfile.Index) :
    Fintype.card (PuncturedIndex J) = 262144 - J.card := by
  classical
  rw [Fintype.card_subtype_compl]
  simp [IRSProfile.Index]

theorem puncturedCode_minDistance (J : Finset IRSProfile.Index)
    (hJ : J.card ≤ 131072) :
    Code.minDist
        (ReedSolomon.code (puncturedDomain J) IRSProfile.baseDimension :
          Set (PuncturedIndex J → IRSProfile.Field)) =
      131073 - J.card := by
  letI : NeZero IRSProfile.baseDimension :=
    ⟨by norm_num [IRSProfile.baseDimension]⟩
  rw [ReedSolomon.minDist_of_le]
  · rw [card_puncturedIndex]
    norm_num [IRSProfile.baseDimension]
    omega
  · rw [card_puncturedIndex]
    norm_num [IRSProfile.baseDimension]
    omega

theorem punctured10_relUDR_ge (J : Finset IRSProfile.Index)
    (hJ : J.card = 10) :
    puncturedRadius10 ≤ Code.relativeUniqueDecodingRadius
      (puncturedCode J : Set (PuncturedIndex J → IRSProfile.Field)) := by
  letI : NeZero IRSProfile.baseDimension :=
    ⟨by norm_num [IRSProfile.baseDimension]⟩
  unfold Code.relativeUniqueDecodingRadius
  rw [ReedSolomon.dist_eq_of_le]
  · rw [card_puncturedIndex J, hJ, ← NNReal.coe_le_coe]
    norm_num [puncturedRadius10, IRSProfile.baseDimension]
  · rw [card_puncturedIndex J, hJ]
    norm_num [IRSProfile.baseDimension]

theorem punctured10_mca_le (J : Finset IRSProfile.Index)
    (hJ : J.card = 10) :
    mcaError (AffineLineGenerator IRSProfile.Field) (puncturedCode J)
        (puncturedRadius10 : ℝ) ≤
      (262134 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  letI : Nonempty (PuncturedIndex J) :=
    Fintype.card_pos_iff.mp (by
      rw [card_puncturedIndex J, hJ]
      norm_num)
  letI : Inhabited (PuncturedIndex J) :=
    Classical.inhabited_of_nonempty
      (inferInstance : Nonempty (PuncturedIndex J))
  letI : NeZero IRSProfile.baseDimension :=
    ⟨by norm_num [IRSProfile.baseDimension]⟩
  have hudr := punctured10_relUDR_ge J hJ
  have hca := RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    (deg := IRSProfile.baseDimension) (domain := puncturedDomain J)
    (δ := puncturedRadius10) hudr
  have heps := (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le
      (F := IRSProfile.Field)
      (puncturedCode J : Set (PuncturedIndex J → IRSProfile.Field))
      puncturedRadius10
      (ProximityGap.errorBound puncturedRadius10 IRSProfile.baseDimension
        (puncturedDomain J))).mp hca
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) (puncturedCode J)
        (puncturedRadius10 : ℝ) ≤
      epsCa (F := IRSProfile.Field)
        (puncturedCode J : Set (PuncturedIndex J → IRSProfile.Field))
        puncturedRadius10 puncturedRadius10 := by
      refine ProximityGap.mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
        (puncturedCode J) puncturedRadius10 ?_ ?_
      · norm_num [puncturedRadius10]
      · rw [ReedSolomon.dist_eq_of_le]
        · rw [card_puncturedIndex J, hJ]
          norm_num [puncturedRadius10, IRSProfile.baseDimension]
        · rw [card_puncturedIndex J, hJ]
          norm_num [IRSProfile.baseDimension]
    _ ≤ (262134 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ProximityGap.errorBound_eq_n_div_q_of_le_relUDR hudr] at heps
      rw [ENNReal.coe_div (by simp), card_puncturedIndex J, hJ] at heps
      exact heps

theorem baseCode_relativeUniqueDecodingRadius_puncture :
    Code.relativeUniqueDecodingRadius
      (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field)) =
      (1 : ℝ≥0) / 4 := by
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, IRSProfile.baseMinDistance]
  apply NNReal.eq
  norm_num

theorem base_mca_quarter_le_puncture :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (1 / 4 : ℝ) ≤
      (262144 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  have hudr : (1 / 4 : ℝ≥0) ≤
      Code.relativeUniqueDecodingRadius
        (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field)) := by
    rw [baseCode_relativeUniqueDecodingRadius_puncture]
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
    _ ≤ (262144 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ProximityGap.errorBound_eq_n_div_q_of_le_relUDR hudr] at heps
      rw [ENNReal.coe_div (by simp)] at heps
      norm_num [IRSProfile.Index] at heps ⊢
      exact heps

open Classical in
theorem fixed_stack_bad_card_le_of_mcaError_le
    {ι F ℓ : Type} [Fintype ι] [Field F] [Fintype F] [Fintype ℓ]
    (G : Generator F ℓ F) (C : ModuleCode ι F F) (δ : ℝ) (a : ℕ)
    (h : mcaError G C δ ≤
      (a : ENNReal) / (Fintype.card F : ENNReal))
    (U : ℓ → ι → F) :
    (Finset.univ.filter fun γ : F => IsMCA G C γ U δ).card ≤ a := by
  have hp : Pr_{let γ ← $ᵖ F}[IsMCA G C γ U δ] ≤
      (a : ENNReal) / (Fintype.card F : ENNReal) :=
    (le_iSup
      (fun V => Pr_{let γ ← $ᵖ F}[IsMCA G C γ V δ]) U).trans h
  rw [Probability.prob_uniform_eq_card_filter_div_card] at hp
  by_contra hnot
  have hltNat :
      a < (Finset.univ.filter fun γ : F => IsMCA G C γ U δ).card :=
    Nat.lt_of_not_ge hnot
  have hlt : (a : ENNReal) <
      ((Finset.univ.filter fun γ : F => IsMCA G C γ U δ).card :
        ENNReal) := by
    exact_mod_cast hltNat
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by simp
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  exact (not_lt_of_ge hp)
    (ENNReal.div_lt_div_right hq0 hqtop hlt)

theorem double_count_relation_mul_le {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (S : Finset α) (J : Finset β) (R : Finset (α × β)) (L B : ℕ)
    (hR : R ⊆ S ×ˢ J)
    (hrow : ∀ x ∈ S, L ≤ (R.filter (fun p => p.1 = x)).card)
    (hcol : ∀ j ∈ J, (R.filter (fun p => p.2 = j)).card ≤ B) :
    S.card * L ≤ J.card * B := by
  have hrowcount :
      (∑ x ∈ S, (R.filter (fun p => p.1 = x)).card) = R.card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hpSJ : p.1 ∈ S ∧ p.2 ∈ J := by
      simpa only [Finset.mem_product] using hR hp
    simp [hpSJ.1]
  have hcolcount :
      (∑ j ∈ J, (R.filter (fun p => p.2 = j)).card) = R.card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hpSJ : p.1 ∈ S ∧ p.2 ∈ J := by
      simpa only [Finset.mem_product] using hR hp
    simp [hpSJ.2]
  calc
    S.card * L = ∑ _x ∈ S, L := by simp
    _ ≤ ∑ x ∈ S, (R.filter (fun p => p.1 = x)).card :=
      Finset.sum_le_sum hrow
    _ = R.card := hrowcount
    _ = ∑ j ∈ J, (R.filter (fun p => p.2 = j)).card :=
      hcolcount.symm
    _ ≤ ∑ _j ∈ J, B := Finset.sum_le_sum hcol
    _ = J.card * B := by simp

open Classical in
theorem large_incidence_bound_generic
    {beta kappa : Type} [Fintype beta] [Fintype kappa]
    [DecidableEq beta] [DecidableEq kappa]
    (S : beta → Finset kappa)
    (hlarge : ∀ b : beta, 65537 ≤ (S b).card)
    (hfixed : ∀ J : Finset kappa, J.card = 10 →
      (Finset.univ.filter fun b : beta => J ⊆ S b).card ≤ 262134) :
    Fintype.card beta * Nat.choose 65537 10 ≤
      262134 * Nat.choose (Fintype.card kappa) 10 := by
  have hdouble :
      (∑ b : beta, Nat.choose (S b).card 10) =
        ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
          (Finset.univ.filter fun b : beta => J ⊆ S b).card := by
    calc
      (∑ b : beta, Nat.choose (S b).card 10) =
          ∑ b : beta, ((S b).powersetCard 10).card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact (Finset.card_powersetCard 10 _).symm
      _ = ∑ b : beta,
          ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
            if J ⊆ S b then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← Finset.card_filter]
        apply congrArg Finset.card
        ext J
        simp only [Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        constructor
        · rintro ⟨hsub, hcard⟩
          exact ⟨hcard, hsub⟩
        · rintro ⟨hcard, hsub⟩
          exact ⟨hsub, hcard⟩
      _ = ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
          ∑ b : beta, if J ⊆ S b then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
          (Finset.univ.filter fun b : beta => J ⊆ S b).card := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.card_filter]
  calc
    Fintype.card beta * Nat.choose 65537 10 =
        ∑ b : beta, Nat.choose 65537 10 := by simp
    _ ≤ ∑ b : beta, Nat.choose (S b).card 10 := by
      apply Finset.sum_le_sum
      intro b hb
      exact Nat.choose_le_choose 10 (hlarge b)
    _ = ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
        (Finset.univ.filter fun b : beta => J ⊆ S b).card := hdouble
    _ ≤ ∑ J ∈ (Finset.univ : Finset kappa).powersetCard 10,
        262134 := by
      apply Finset.sum_le_sum
      intro J hJ
      exact hfixed J (Finset.mem_powersetCard.mp hJ).2
    _ = 262134 * Nat.choose (Fintype.card kappa) 10 := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [Nat.mul_comm]

theorem fixed10_numerator_le_two_pow_39 :
    262144 +
      (Nat.choose 262144 10 * 262134) / Nat.choose 65537 10 ≤
        2 ^ 39 := by
  norm_num [Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]

def restrictWord (J : Finset IRSProfile.Index)
    (w : IRSProfile.Index → IRSProfile.Field) :
    PuncturedIndex J → IRSProfile.Field :=
  fun i => w i.1

theorem restrictWord_mem_puncturedCode (J : Finset IRSProfile.Index)
    {w : IRSProfile.Index → IRSProfile.Field}
    (hw : w ∈ IRSProfile.baseCode) :
    restrictWord J w ∈
      ReedSolomon.code (puncturedDomain J) IRSProfile.baseDimension := by
  change w ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hw
  rw [ReedSolomon.mem_code_iff_eval] at hw ⊢
  obtain ⟨p, hpdeg, hp⟩ := hw
  refine ⟨p, hpdeg, ?_⟩
  intro i
  simpa [restrictWord, puncturedDomain] using hp i.1

theorem exists_baseCode_extension (J : Finset IRSProfile.Index)
    {w : PuncturedIndex J → IRSProfile.Field}
    (hw : w ∈ ReedSolomon.code (puncturedDomain J)
      IRSProfile.baseDimension) :
    ∃ w' ∈ IRSProfile.baseCode, restrictWord J w' = w := by
  rw [ReedSolomon.mem_code_iff_eval] at hw
  obtain ⟨p, hpdeg, hp⟩ := hw
  let w' : IRSProfile.Index → IRSProfile.Field :=
    fun i => p.eval (IRSProfile.domain i)
  have hw' : w' ∈ IRSProfile.baseCode := by
    rw [IRSProfile.baseCode, ReedSolomon.mem_code_iff_eval]
    exact ⟨p, hpdeg, by intro i; rfl⟩
  refine ⟨w', hw', funext fun i => ?_⟩
  simpa [restrictWord, puncturedDomain, w'] using hp i

theorem exists_fullAgreement_witness
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (γ : IRSProfile.Field)
    (h : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode γ U ((2731 : ℝ) / 10923)) :
    ∃ w ∈ IRSProfile.baseCode,
      let E := Code.disagreementCols (U 0 + γ • U 1) w
      E.card ≤ 65541 ∧
        LinearCode.projectedWord (U 0 + γ • U 1) Eᶜ ∈
          LinearCode.projectedCodeSubmod IRSProfile.baseCode Eᶜ ∧
        ∃ j : Fin 2,
          LinearCode.projectedWord (U j) Eᶜ ∉
            LinearCode.projectedCodeSubmod IRSProfile.baseCode Eᶜ := by
  classical
  obtain ⟨T, hT, hcomb, hbad⟩ := h
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨w, hw, hproj⟩ := hcomb
  let E := Code.disagreementCols (U 0 + γ • U 1) w
  have hTsub : T ⊆ Eᶜ := by
    intro i hiT
    rw [Finset.mem_compl]
    intro hiE
    have heq := congr_fun hproj ⟨i, hiT⟩
    exact (Code.mem_disagreementCols.mp hiE) (by
      simpa [E, LinearCode.projectedWord, AffineLineGenerator] using heq)
  have hEsub : E ⊆ Tᶜ := by
    intro i hiE
    rw [Finset.mem_compl]
    intro hiT
    exact (Finset.mem_compl.mp (hTsub hiT)) hiE
  have hTcomp : Tᶜ.card ≤ 65541 := by
    have hfloor := hT
    rw [CoreDefinitions.mul_one_sub_le_card_iff_sub_card_le_floor
      T (by norm_num : (0 : ℝ) ≤ (2731 : ℝ) / 10923)] at hfloor
    rw [show Fintype.card IRSProfile.Index = 262144 by
      norm_num [IRSProfile.Index]] at hfloor
    norm_num at hfloor
    simpa [Finset.card_compl] using hfloor
  have hEcard : E.card ≤ 65541 :=
    (Finset.card_le_card hEsub).trans hTcomp
  refine ⟨w, hw, hEcard, ?_, ?_⟩
  · rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨w, hw, funext fun i => ?_⟩
    have hi : (U 0 + γ • U 1) i.1 = w i.1 := by
      by_contra hne
      exact (Finset.mem_compl.mp i.2)
        (Code.mem_disagreementCols.mpr hne)
    simpa [LinearCode.projectedWord] using hi
  · obtain ⟨j, hj⟩ := hbad
    refine ⟨j, ?_⟩
    intro hfull
    apply hj
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hfull ⊢
    obtain ⟨c, hc, hcproj⟩ := hfull
    refine ⟨c, hc, funext fun i => ?_⟩
    have heq := congr_fun hcproj ⟨i.1, hTsub i.2⟩
    simpa [LinearCode.projectedWord] using heq

set_option maxHeartbeats 1000000 in
theorem fullAgreement_isMCA_quarter
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (γ : IRSProfile.Field) (E : Finset IRSProfile.Index)
    (hE : E.card ≤ 65536)
    (hcomb : LinearCode.projectedWord (U 0 + γ • U 1) Eᶜ ∈
      LinearCode.projectedCodeSubmod IRSProfile.baseCode Eᶜ)
    (hbad : ∃ j : Fin 2, LinearCode.projectedWord (U j) Eᶜ ∉
      LinearCode.projectedCodeSubmod IRSProfile.baseCode Eᶜ) :
    IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
      γ U (1 / 4 : ℝ) := by
  have hline :
      (fun k => ∑ j, AffineLineGenerator IRSProfile.Field γ j • U j k) =
        U 0 + γ • U 1 := by
    funext i
    simp [AffineLineGenerator, Fin.sum_univ_two]
  refine ⟨Eᶜ, ?_, ?_, hbad⟩
  · rw [Finset.card_compl]
    norm_num [IRSProfile.Index]
    exact_mod_cast (show 196608 ≤ 262144 - E.card by omega)
  · rw [hline]
    exact hcomb

noncomputable abbrev postQuarterRadius5 : ℝ≥0 :=
  (65541 : ℝ≥0) / 262144

structure IRSBadWitness (gamma : IRSProfile.Field)
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) where
  cols : Finset IRSProfile.Index
  card_bound : 196603 ≤ cols.card
  codeword : IRSProfile.baseCode
  fold_agree : ∀ i ∈ cols,
    U 0 i + gamma • U 1 i = codeword.1 i
  row_not_projected : ∃ j : Fin 2,
    LinearCode.projectedWord (U j) cols ∉
      LinearCode.projectedCodeSubmod IRSProfile.baseCode cols

open Classical in
theorem IRSBadWitness.of_isMCA
    (gamma : IRSProfile.Field)
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (h : IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode gamma U (postQuarterRadius5 : ℝ)) :
    Nonempty (IRSBadWitness gamma U) := by
  obtain ⟨T, hT, hcomb, hrow⟩ := h
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨c, hc, hproj⟩ := hcomb
  have hTnat : 196603 ≤ T.card := by
    norm_num [postQuarterRadius5, IRSProfile.Index] at hT
    exact_mod_cast hT
  refine ⟨{
    cols := T
    card_bound := hTnat
    codeword := ⟨c, hc⟩
    fold_agree := ?_
    row_not_projected := hrow }⟩
  intro i hi
  have hiProj := congrFun hproj ⟨i, hi⟩
  simpa [AffineLineGenerator, Fin.sum_univ_two,
    LinearCode.projectedWord] using hiProj

def IRSBadWitness.errors {gamma : IRSProfile.Field}
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (w : IRSBadWitness gamma U) : Finset IRSProfile.Index :=
  Code.disagreementCols (U 0 + gamma • U 1) w.codeword.1

open Classical in
theorem IRSBadWitness.errors_card_le {gamma : IRSProfile.Field}
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (w : IRSBadWitness gamma U) : w.errors.card ≤ 65541 := by
  have hsub : w.errors ⊆ w.colsᶜ := by
    intro i hi
    simp only [Finset.mem_compl]
    intro hiT
    have hne := Code.mem_disagreementCols.mp hi
    exact hne (by simpa using w.fold_agree i hiT)
  calc
    w.errors.card ≤ w.colsᶜ.card := Finset.card_le_card hsub
    _ = 262144 - w.cols.card := by
      rw [Finset.card_compl]
      simp [IRSProfile.Index]
    _ ≤ 65541 := by
      have hcolsle : w.cols.card ≤ 262144 := by
        simpa [IRSProfile.Index] using Finset.card_le_univ w.cols
      have hbound := w.card_bound
      omega

open Classical in
theorem IRSBadWitness.quarter_isMCA
    {gamma : IRSProfile.Field}
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (w : IRSBadWitness gamma U) (hsmall : w.errors.card ≤ 65536) :
    IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
      gamma U (1 / 4 : ℝ) := by
  have hcols : w.cols ⊆ w.errorsᶜ := by
    intro i hiT
    rw [Finset.mem_compl]
    intro hiE
    exact (Code.mem_disagreementCols.mp hiE)
      (by simpa using w.fold_agree i hiT)
  have hcomb :
      LinearCode.projectedWord (U 0 + gamma • U 1) w.errorsᶜ ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode w.errorsᶜ := by
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨w.codeword.1, w.codeword.2, funext fun i => ?_⟩
    have hi : (U 0 + gamma • U 1) i.1 = w.codeword.1 i.1 := by
      by_contra hne
      exact (Finset.mem_compl.mp i.2)
        (Code.mem_disagreementCols.mpr hne)
    simpa [LinearCode.projectedWord] using hi
  have hbad : ∃ j : Fin 2,
      LinearCode.projectedWord (U j) w.errorsᶜ ∉
        LinearCode.projectedCodeSubmod IRSProfile.baseCode w.errorsᶜ := by
    obtain ⟨j, hj⟩ := w.row_not_projected
    refine ⟨j, ?_⟩
    intro hfull
    apply hj
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hfull ⊢
    obtain ⟨c, hc, hcproj⟩ := hfull
    refine ⟨c, hc, funext fun i => ?_⟩
    have heq := congrFun hcproj ⟨i.1, hcols i.2⟩
    simpa [LinearCode.projectedWord] using heq
  exact fullAgreement_isMCA_quarter U gamma w.errors hsmall hcomb hbad

open Classical in
theorem IRSBadWitness.punctured_isMCA
    {gamma : IRSProfile.Field}
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (w : IRSBadWitness gamma U)
    (J : Finset IRSProfile.Index) (hJcard : J.card = 10)
    (hJE : J ⊆ w.errors) :
    IsMCA (AffineLineGenerator IRSProfile.Field) (puncturedCode J) gamma
      (fun j => restrictWord J (U j)) (puncturedRadius10 : ℝ) := by
  have hJT : ∀ i ∈ w.cols, i ∉ J := by
    intro i hiT hiJ
    have hiE := hJE hiJ
    exact (Code.mem_disagreementCols.mp hiE)
      (by simpa using w.fold_agree i hiT)
  let e : w.cols ↪ PuncturedIndex J :=
    ⟨fun i => ⟨i.1, hJT i.1 i.2⟩,
      fun a b h => by
        apply Subtype.ext
        exact congrArg (fun x : PuncturedIndex J => x.1) h⟩
  let T' : Finset (PuncturedIndex J) := Finset.univ.map e
  have hT'card : T'.card = w.cols.card := by
    simp [T']
  have hT'mem (i : w.cols) : e i ∈ T' := by
    simp [T']
  have hline :
      (fun k => ∑ j, AffineLineGenerator IRSProfile.Field gamma j •
        restrictWord J (U j) k) =
      restrictWord J (U 0 + gamma • U 1) := by
    funext i
    simp [AffineLineGenerator, Fin.sum_univ_two, restrictWord]
  refine ⟨T', ?_, ?_, ?_⟩
  · rw [hT'card, card_puncturedIndex J, hJcard]
    norm_num [puncturedRadius10]
    exact w.card_bound
  · rw [hline]
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨restrictWord J w.codeword.1,
      restrictWord_mem_puncturedCode J w.codeword.2, ?_⟩
    funext i
    obtain ⟨k, hk⟩ := Finset.mem_map.mp i.2
    have hki : e k = i.1 := hk.2
    have hval : k.1 = i.1.1 :=
      congrArg (fun x : PuncturedIndex J => x.1) hki
    have hagree := w.fold_agree k.1 k.2
    change (U 0 + gamma • U 1) i.1.1 = w.codeword.1 i.1.1
    rw [← hval]
    simpa using hagree
  · obtain ⟨j, hj⟩ := w.row_not_projected
    refine ⟨j, ?_⟩
    intro hp
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hp
    obtain ⟨c, hc, hproj⟩ := hp
    obtain ⟨c', hc', hc'restrict⟩ := exists_baseCode_extension J hc
    apply hj
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨c', hc', funext fun i => ?_⟩
    let ip : PuncturedIndex J := e i
    let iT' : T' := ⟨ip, hT'mem i⟩
    have hp_i := congrFun hproj iT'
    have hc_i := congrFun hc'restrict ip
    change U j i.1 = c' i.1
    simpa [LinearCode.projectedWord, restrictWord, ip, iT', e] using
      hp_i.trans hc_i.symm

def IsPostQuarterBad
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field) : Prop :=
  IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
    gamma U (postQuarterRadius5 : ℝ)

abbrev PostQuarterBadSlope
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) :=
  {gamma : IRSProfile.Field // IsPostQuarterBad U gamma}

noncomputable def postQuarterWitness
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : PostQuarterBadSlope U) : IRSBadWitness gamma.1 U :=
  Classical.choice (IRSBadWitness.of_isMCA gamma.1 U gamma.2)

open Classical in
set_option maxRecDepth 10000 in
theorem fixed_stack_postQuarter_bad_card_le
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) :
    (Finset.univ.filter fun gamma : IRSProfile.Field =>
      IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        gamma U (postQuarterRadius5 : ℝ)).card ≤ 2 ^ 39 := by
  let p : PostQuarterBadSlope U → Prop := fun gamma =>
    (postQuarterWitness U gamma).errors.card ≤ 65536
  let Small := {gamma : PostQuarterBadSlope U // p gamma}
  let Large := {gamma : PostQuarterBadSlope U // ¬p gamma}
  have hpart : Fintype.card (PostQuarterBadSlope U) =
      Fintype.card Small + Fintype.card Large := by
    have hcomp : Fintype.card Large =
        Fintype.card (PostQuarterBadSlope U) - Fintype.card Small := by
      simp [Small, Large, Fintype.card_subtype_compl]
    have hsmallle : Fintype.card Small ≤
        Fintype.card (PostQuarterBadSlope U) := by
      simpa [Small] using Fintype.card_subtype_le p
    omega
  let Q := {gamma : IRSProfile.Field //
    IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
      gamma U (1 / 4 : ℝ)}
  have hQ : Fintype.card Q ≤ 262144 := by
    calc
      Fintype.card Q =
          (Finset.univ.filter fun gamma : IRSProfile.Field =>
            IsMCA (AffineLineGenerator IRSProfile.Field)
              IRSProfile.baseCode gamma U (1 / 4 : ℝ)).card := by
        simpa [Q] using Fintype.card_subtype
          (fun gamma : IRSProfile.Field =>
            IsMCA (AffineLineGenerator IRSProfile.Field)
              IRSProfile.baseCode gamma U (1 / 4 : ℝ))
      _ ≤ 262144 := fixed_stack_bad_card_le_of_mcaError_le
        (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (1 / 4 : ℝ) 262144 base_mca_quarter_le_puncture U
  have hSmall : Fintype.card Small ≤ 262144 := by
    let f : Small → Q := fun gamma =>
      ⟨gamma.1.1, (postQuarterWitness U gamma.1).quarter_isMCA gamma.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg (fun q : Q => q.1) hab
      simpa [f] using hval
    exact (Fintype.card_le_of_injective f hf).trans hQ
  have hfixed (J : Finset IRSProfile.Index) (hJ : J.card = 10) :
      (Finset.univ.filter fun gamma : Large =>
        J ⊆ (postQuarterWitness U gamma.1).errors).card ≤ 262134 := by
    let QJ := {gamma : IRSProfile.Field //
      IsMCA (AffineLineGenerator IRSProfile.Field) (puncturedCode J) gamma
        (fun j => restrictWord J (U j)) (puncturedRadius10 : ℝ)}
    have hQJ : Fintype.card QJ ≤ 262134 := by
      calc
        Fintype.card QJ =
            (Finset.univ.filter fun gamma : IRSProfile.Field =>
              IsMCA (AffineLineGenerator IRSProfile.Field) (puncturedCode J)
                gamma (fun j => restrictWord J (U j))
                  (puncturedRadius10 : ℝ)).card := by
          simpa [QJ] using Fintype.card_subtype
            (fun gamma : IRSProfile.Field =>
              IsMCA (AffineLineGenerator IRSProfile.Field) (puncturedCode J)
                gamma (fun j => restrictWord J (U j))
                  (puncturedRadius10 : ℝ))
        _ ≤ 262134 := fixed_stack_bad_card_le_of_mcaError_le
          (AffineLineGenerator IRSProfile.Field) (puncturedCode J)
          (puncturedRadius10 : ℝ) 262134 (punctured10_mca_le J hJ)
          (fun j => restrictWord J (U j))
    let S := {gamma : Large //
      J ⊆ (postQuarterWitness U gamma.1).errors}
    let f : S → QJ := fun gamma =>
      ⟨gamma.1.1.1,
        (postQuarterWitness U gamma.1.1).punctured_isMCA J hJ gamma.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg (fun q : QJ => q.1) hab
      simpa [f] using hval
    have hScard : Fintype.card S ≤ 262134 :=
      (Fintype.card_le_of_injective f hf).trans hQJ
    rw [← show Fintype.card S =
        (Finset.univ.filter fun gamma : Large =>
          J ⊆ (postQuarterWitness U gamma.1).errors).card by
      simpa [S] using Fintype.card_subtype
        (fun gamma : Large =>
          J ⊆ (postQuarterWitness U gamma.1).errors)]
    exact hScard
  have hlarge (gamma : Large) :
      65537 ≤ (postQuarterWitness U gamma.1).errors.card := by
    have hn : ¬(postQuarterWitness U gamma.1).errors.card ≤ 65536 := by
      simpa [p] using gamma.2
    omega
  have hinc := large_incidence_bound_generic
    (beta := Large) (kappa := IRSProfile.Index)
    (S := fun gamma => (postQuarterWitness U gamma.1).errors) hlarge hfixed
  have hinc' :
      Fintype.card Large * Nat.choose 65537 10 ≤
        262134 * Nat.choose 262144 10 := by
    simpa [IRSProfile.Index] using hinc
  have hnum :
      262134 * Nat.choose 262144 10 ≤
        274967056148 * Nat.choose 65537 10 := by
    norm_num [Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial]
  have hLarge : Fintype.card Large ≤ 274967056148 := by
    apply Nat.le_of_mul_le_mul_right (hinc'.trans hnum)
    exact Nat.choose_pos (by norm_num)
  have hB : Fintype.card (PostQuarterBadSlope U) ≤ 2 ^ 39 := by
    rw [hpart]
    exact (Nat.add_le_add hSmall hLarge).trans (by norm_num)
  simpa [PostQuarterBadSlope, IsPostQuarterBad,
    Fintype.card_subtype] using hB

theorem base_mca_postQuarter_le_two_pow_39 :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (postQuarterRadius5 : ℝ) ≤
      (2 : ENNReal) ^ 39 /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  classical
  unfold mcaError
  apply iSup_le
  intro U
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast fixed_stack_postQuarter_bad_card_le U

end

end ProximityPrize.SubmissionLower
