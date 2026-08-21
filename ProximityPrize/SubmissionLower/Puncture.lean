import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal ProbabilityTheory

set_option linter.unusedSectionVars false

section Puncture

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

noncomputable def puncturedDomain (domain : ι ↪ F) (P : Finset ι) :
    {i : ι // i ∉ P} ↪ F :=
  (Function.Embedding.subtype fun i : ι => i ∉ P).trans domain

def restrictWord (P : Finset ι) (u : ι → F) : {i : ι // i ∉ P} → F :=
  fun i => u i.1

lemma restrictWord_mem_code {domain : ι ↪ F} {k : ℕ} {P : Finset ι}
    {u : ι → F} (hu : u ∈ ReedSolomon.code domain k) :
    restrictWord P u ∈ ReedSolomon.code (puncturedDomain domain P) k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hu ⊢
  obtain ⟨p, hp, rfl⟩ := hu
  exact ⟨p, hp, rfl⟩


lemma exists_bad_subset_card_eq {domain : ι ↪ F} {k a : ℕ}
    (hk : 0 < k) (hka : k + 1 ≤ a) {S₀ : Finset ι} (haS : a ≤ S₀.card)
    (u : ι → F)
    (hu : LinearCode.projectedWord u S₀ ∉
      LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S₀) :
    ∃ S : Finset ι, S ⊆ S₀ ∧ S.card = a ∧
      LinearCode.projectedWord u S ∉
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S := by
  classical
  obtain ⟨K, hKS₀, hKcard⟩ :=
    Finset.exists_subset_card_eq (s := S₀) (n := k) (by omega)
  let q : Polynomial F := Lagrange.interpolate K domain u
  have hqdeg : q.natDegree < k := by
    by_cases hq : q = 0
    · simp [hq, hk]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hq, ← hKcard]
      exact Lagrange.degree_interpolate_lt u domain.injective.injOn
  have hqdegree : q.degree < k := by
    by_cases hq : q = 0
    · simp [hq]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hq).mp hqdeg
  have hqmem : ReedSolomon.evalOnPoints domain q ∈ ReedSolomon.code domain k :=
    ReedSolomon.evalOnPoints_mem_code_of_degree_lt hqdegree
  have hx : ∃ x ∈ S₀, q.eval (domain x) ≠ u x := by
    by_contra h
    push Not at h
    apply hu
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨ReedSolomon.evalOnPoints domain q, hqmem, ?_⟩
    funext i
    simp only [LinearCode.projectedWord, Set.restrict_apply, ReedSolomon.evalOnPoints]
    exact (h i.1 i.2).symm
  obtain ⟨x, hxS₀, hxneq⟩ := hx
  have hxK : x ∉ K := by
    intro hxK
    exact hxneq (Lagrange.eval_interpolate_at_node u domain.injective.injOn hxK)
  have hinsert_sub : insert x K ⊆ S₀ := Finset.insert_subset hxS₀ hKS₀
  have hinsert_card : (insert x K).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hxK, hKcard]
  obtain ⟨S, hsubS, hSS₀, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hinsert_sub (by omega) haS
  refine ⟨S, hSS₀, hScard, ?_⟩
  intro huS
  rw [LinearCode.mem_projectedCodeSubmod_iff] at huS
  obtain ⟨c, hc, hcu⟩ := huS
  change c ∈ ReedSolomon.code domain k at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨p, hpdegree, rfl⟩ := hc
  have hpdeg : p.natDegree < k := by
    by_cases hp : p = 0
    · simp [hp, hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hpdegree
  have hpq : p = q := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
      (f := fun i : ↥K => domain i.1) ?_ ?_ ?_
    · intro i j hij
      exact Subtype.ext (domain.injective hij)
    · intro i
      have hiS : i.1 ∈ S := hsubS (Finset.mem_insert_of_mem i.2)
      have hcui := congrFun hcu ⟨i.1, hiS⟩
      simpa [q, LinearCode.projectedWord, ReedSolomon.evalOnPoints] using
        hcui.symm.trans
          (Lagrange.eval_interpolate_at_node u domain.injective.injOn i.2).symm
    · rw [Fintype.card_coe, hKcard]
      exact max_lt hpdeg hqdeg
  have hxS : x ∈ S := hsubS (Finset.mem_insert_self x K)
  have hcx := congrFun hcu ⟨x, hxS⟩
  apply hxneq
  simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints, hpq] using hcx.symm

lemma exists_exact_mca_support_rs {domain : ι ↪ F} {k a : ℕ}
    (hk : 0 < k) (hka : k + 1 ≤ a)
    {δ : ℝ} {γ : F} {U : Fin 2 → ι → F}
    (hsize : ∀ T : Finset ι,
      (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - δ) → a ≤ T.card)
    (hmca : IsMCA (AffineLineGenerator F)
      (ReedSolomon.code domain k) γ U δ) :
    ∃ S : Finset ι, S.card = a ∧
      LinearCode.projectedWord
          (fun x => ∑ j, AffineLineGenerator F γ j • U j x) S ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S ∧
      ∃ j : Fin 2, LinearCode.projectedWord (U j) S ∉
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S := by
  obtain ⟨T, hTsize, hcomb, j, hj⟩ := hmca
  have haT : a ≤ T.card := hsize T hTsize
  obtain ⟨S, hST, hScard, hjS⟩ :=
    exists_bad_subset_card_eq hk hka haT (U j) hj
  refine ⟨S, hScard, ?_, j, hjS⟩
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb ⊢
  obtain ⟨c, hc, hceq⟩ := hcomb
  refine ⟨c, hc, ?_⟩
  funext i
  exact congrFun hceq ⟨i.1, hST i.2⟩

def puncturedSupportEmbedding {P S : Finset ι} (hPS : Disjoint P S) :
    ↥S ↪ {i : ι // i ∉ P} where
  toFun i := ⟨i.1, fun hiP => Finset.disjoint_left.mp hPS hiP i.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {i : ι // i ∉ P} => z.1) h

def puncturedSupport {P S : Finset ι} (hPS : Disjoint P S) :
    Finset {i : ι // i ∉ P} :=
  S.attach.map (puncturedSupportEmbedding hPS)

@[simp] lemma card_puncturedSupport {P S : Finset ι} (hPS : Disjoint P S) :
    (puncturedSupport hPS).card = S.card := by
  simp [puncturedSupport]

lemma mem_puncturedSupport_iff {P S : Finset ι} (hPS : Disjoint P S)
    (i : {i : ι // i ∉ P}) :
    i ∈ puncturedSupport hPS ↔ i.1 ∈ S := by
  classical
  rw [puncturedSupport, Finset.mem_map]
  constructor
  · rintro ⟨x, _, hx⟩
    have := congrArg (fun z : {i : ι // i ∉ P} => z.1) hx
    simpa using this ▸ x.2
  · intro hi
    let x : ↥S := ⟨i.1, hi⟩
    refine ⟨x, Finset.mem_attach S x, ?_⟩
    apply Subtype.ext
    rfl

lemma projected_restrict_mem_iff {domain : ι ↪ F} {k : ℕ}
    {P S : Finset ι} (hPS : Disjoint P S) (u : ι → F) :
    LinearCode.projectedWord (restrictWord P u) (puncturedSupport hPS) ∈
        LinearCode.projectedCodeSubmod
          (ReedSolomon.code (puncturedDomain domain P) k) (puncturedSupport hPS) ↔
      LinearCode.projectedWord u S ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S := by
  classical
  rw [LinearCode.mem_projectedCodeSubmod_iff,
    LinearCode.mem_projectedCodeSubmod_iff]
  constructor
  · rintro ⟨c, hc, hcu⟩
    change c ∈ ReedSolomon.code (puncturedDomain domain P) k at hc
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    let cFull := ReedSolomon.evalOnPoints domain p
    have hcFull : cFull ∈ ReedSolomon.code domain k :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt hp
    refine ⟨cFull, hcFull, ?_⟩
    funext i
    let iP : {x : ι // x ∉ P} :=
      ⟨i.1, fun hiP => Finset.disjoint_left.mp hPS hiP i.2⟩
    have hiSP : iP ∈ puncturedSupport hPS :=
      (mem_puncturedSupport_iff hPS iP).mpr i.2
    have heq := congrFun hcu ⟨iP, hiSP⟩
    simpa [LinearCode.projectedWord, restrictWord, puncturedDomain, cFull,
      ReedSolomon.evalOnPoints, iP] using heq
  · rintro ⟨c, hc, hcu⟩
    have hcP := restrictWord_mem_code (P := P) hc
    refine ⟨restrictWord P c, hcP, ?_⟩
    funext i
    have hiS : i.1.1 ∈ S := (mem_puncturedSupport_iff hPS i.1).mp i.2
    have heq := congrFun hcu ⟨i.1.1, hiS⟩
    simpa [LinearCode.projectedWord, restrictWord] using heq

lemma isMCA_punctured_of_exact_support {domain : ι ↪ F} {k : ℕ}
    {P S : Finset ι} (hPS : Disjoint P S) {δp : ℝ} {γ : F}
    {U : Fin 2 → ι → F}
    (hsizeP : (S.card : ℝ) ≥
      (Fintype.card {i : ι // i ∉ P} : ℝ) * (1 - δp))
    (hcomb :
      LinearCode.projectedWord
          (fun x => ∑ j, AffineLineGenerator F γ j • U j x) S ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S)
    (hbad : ∃ j : Fin 2, LinearCode.projectedWord (U j) S ∉
      LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S) :
    IsMCA (AffineLineGenerator F)
      (ReedSolomon.code (puncturedDomain domain P) k) γ
      (fun j => restrictWord P (U j)) δp := by
  refine ⟨puncturedSupport hPS, ?_, ?_, ?_⟩
  · simpa using hsizeP
  · have hp := (projected_restrict_mem_iff hPS
      (fun x => ∑ j, AffineLineGenerator F γ j • U j x)).mpr hcomb
    convert hp using 1
    ext i
    simp [LinearCode.projectedWord, restrictWord, AffineLineGenerator, Fin.sum_univ_two]
  · obtain ⟨j, hj⟩ := hbad
    refine ⟨j, ?_⟩
    intro hp
    apply hj
    apply (projected_restrict_mem_iff hPS (U j)).mp
    simpa using hp

lemma card_puncturedIndex (P : Finset IRSProfile.Index) (hP : P.card = 10) :
    Fintype.card {i : IRSProfile.Index // i ∉ P} = 262134 := by
  simp only [Fintype.card_subtype_compl]
  rw [Fintype.card_coe, hP]
  norm_num [IRSProfile.Index]

noncomputable def puncturedRadius : ℝ≥0 := (65531 : ℝ≥0) / 262134

lemma punctured_relativeUniqueDecodingRadius
    (P : Finset IRSProfile.Index) (hP : P.card = 10) :
    Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
        IRSProfile.baseDimension :
        Set ({i : IRSProfile.Index // i ∉ P} → IRSProfile.Field)) =
      puncturedRadius := by
  have hcard := card_puncturedIndex P hP
  letI : Nonempty {i : IRSProfile.Index // i ∉ P} :=
    Fintype.card_pos_iff.mp (by omega)
  letI : Inhabited {i : IRSProfile.Index // i ∉ P} :=
    Classical.inhabited_of_nonempty ‹Nonempty {i : IRSProfile.Index // i ∉ P}›
  letI : NeZero IRSProfile.baseDimension :=
    ⟨by norm_num [IRSProfile.baseDimension]⟩
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, ReedSolomon.minDist_eq_card_sub_min_add_1,
    card_puncturedIndex P hP]
  apply NNReal.eq
  norm_num [puncturedRadius, IRSProfile.baseDimension]

lemma punctured_mca_le
    (P : Finset IRSProfile.Index) (hP : P.card = 10) :
    mcaError (AffineLineGenerator IRSProfile.Field)
        (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
          IRSProfile.baseDimension) (puncturedRadius : ℝ) ≤
      (262134 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  let J := {i : IRSProfile.Index // i ∉ P}
  have hJcard : Fintype.card J = 262134 := card_puncturedIndex P hP
  letI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  letI : Inhabited J := Classical.inhabited_of_nonempty ‹Nonempty J›
  letI : NeZero IRSProfile.baseDimension :=
    ⟨by norm_num [IRSProfile.baseDimension]⟩
  have hudr : puncturedRadius ≤
      Code.relativeUniqueDecodingRadius
        (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
          IRSProfile.baseDimension : Set (J → IRSProfile.Field)) := by
    rw [punctured_relativeUniqueDecodingRadius P hP]
  have hca :=
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime
      (deg := IRSProfile.baseDimension)
      (domain := puncturedDomain IRSProfile.domain P)
      (δ := puncturedRadius) hudr
  have heps :=
    (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le
      (F := IRSProfile.Field)
      (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
        IRSProfile.baseDimension : Set (J → IRSProfile.Field))
      puncturedRadius
      (ProximityGap.errorBound puncturedRadius IRSProfile.baseDimension
        (puncturedDomain IRSProfile.domain P))).mp hca
  rw [ProximityGap.errorBound_eq_n_div_q_of_le_relUDR hudr] at heps
  rw [ENNReal.coe_div (by simp), hJcard] at heps
  refine (mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
    (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
      IRSProfile.baseDimension) puncturedRadius (by norm_num [puncturedRadius]) ?_).trans heps
  rw [Code.dist_eq_minDist, ReedSolomon.minDist_eq_card_sub_min_add_1, hJcard]
  norm_num [puncturedRadius, IRSProfile.baseDimension]

set_option maxRecDepth 100000 in
open Classical in
lemma punctured_bad_card_le
    (P : Finset IRSProfile.Index) (hP : P.card = 10)
    (U : Fin 2 → {i : IRSProfile.Index // i ∉ P} → IRSProfile.Field) :
    (Finset.univ.filter fun γ : IRSProfile.Field =>
      IsMCA (AffineLineGenerator IRSProfile.Field)
        (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
          IRSProfile.baseDimension) γ U (puncturedRadius : ℝ)).card ≤ 262134 := by
  classical
  let B := Finset.univ.filter fun γ : IRSProfile.Field =>
    IsMCA (AffineLineGenerator IRSProfile.Field)
      (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
        IRSProfile.baseDimension) γ U (puncturedRadius : ℝ)
  change B.card ≤ 262134
  let J := {i : IRSProfile.Index // i ∉ P}
  have hJcard : Fintype.card J = 262134 := card_puncturedIndex P hP
  letI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hprob :
      Pr_{let γ ←$ᵖ IRSProfile.Field}[
        IsMCA (AffineLineGenerator IRSProfile.Field)
          (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
            IRSProfile.baseDimension) γ U (puncturedRadius : ℝ)] ≤
        (262134 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
    exact (le_iSup
      (fun V : Fin 2 → J → IRSProfile.Field =>
        Pr_{let γ ←$ᵖ IRSProfile.Field}[
          IsMCA (AffineLineGenerator IRSProfile.Field)
            (ReedSolomon.code (puncturedDomain IRSProfile.domain P)
              IRSProfile.baseDimension) γ V (puncturedRadius : ℝ)]) U).trans
      (punctured_mca_le P hP)
  rw [Probability.prob_uniform_eq_card_filter_div_card] at hprob
  change (B.card : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) ≤
    (262134 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) at hprob
  have hmul := mul_le_mul_right' hprob (Fintype.card IRSProfile.Field : ENNReal)
  have hq0 : (Fintype.card IRSProfile.Field : ENNReal) ≠ 0 := by simp
  have hqtop : (Fintype.card IRSProfile.Field : ENNReal) ≠ ⊤ := by simp
  rw [ENNReal.div_mul_cancel hq0 hqtop] at hmul
  rw [ENNReal.div_mul_cancel hq0 hqtop] at hmul
  have hNN : (B.card : ℝ≥0) ≤ (262134 : ℝ≥0) := by
    rw [← ENNReal.coe_le_coe]
    exact hmul
  exact_mod_cast hNN

def punctureFinset {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin 10 ↪ ι) : Finset ι :=
  Finset.univ.map e

@[simp] lemma card_punctureFinset {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin 10 ↪ ι) : (punctureFinset e).card = 10 := by
  simp [punctureFinset]

def validPunctureEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    {e : Fin 10 ↪ ι // Disjoint (punctureFinset e) S} ≃
      (Fin 10 ↪ {i : ι // i ∉ S}) where
  toFun e :=
    { toFun := fun i => ⟨e.1 i, fun hiS => by
        apply Finset.disjoint_left.mp e.2
        · exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
        · exact hiS⟩
      inj' := fun _ _ h => e.1.injective (congrArg Subtype.val h) }
  invFun e :=
    ⟨e.trans (Function.Embedding.subtype fun i : ι => i ∉ S), by
      rw [Finset.disjoint_left]
      intro x hx hiS
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact (e i).2 hiS⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    rfl
  right_inv e := by
    ext i
    rfl

lemma card_validPunctures {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    (Finset.univ.filter fun e : Fin 10 ↪ ι =>
      Disjoint (punctureFinset e) S).card =
        (Fintype.card ι - S.card).descFactorial 10 := by
  classical
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {e : Fin 10 ↪ ι // Disjoint (punctureFinset e) S} =
        Fintype.card (Fin 10 ↪ {i : ι // i ∉ S}) :=
      Fintype.card_congr (validPunctureEquiv S)
    _ = (Fintype.card ι - S.card).descFactorial 10 := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_subtype_compl, Fintype.card_coe]

lemma incidence_double_count {α β : Type} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (A : Finset β) (valid : α → β → Prop)
    [DecidableRel valid]
    (L M : ℕ)
    (hlower : ∀ x ∈ B, L ≤ (A.filter fun y => valid x y).card)
    (hupper : ∀ y ∈ A, (B.filter fun x => valid x y).card ≤ M) :
    B.card * L ≤ A.card * M := by
  classical
  calc
    B.card * L = ∑ _x ∈ B, L := by simp
    _ ≤ ∑ x ∈ B, (A.filter fun y => valid x y).card :=
      Finset.sum_le_sum hlower
    _ = ∑ x ∈ B, ∑ y ∈ A, if valid x y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp
    _ = ∑ y ∈ A, ∑ x ∈ B, if valid x y then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ A, (B.filter fun x => valid x y).card := by
      apply Finset.sum_congr rfl
      intro y hy
      simp
    _ ≤ ∑ _y ∈ A, M := Finset.sum_le_sum hupper
    _ = A.card * M := by simp

noncomputable def improvedRadius : ℝ≥0 := (262167 : ℝ≥0) / 1048576

lemma improvedRadius_floor :
    ⌊(improvedRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 65541 := by
  norm_num [improvedRadius, IRSProfile.Index]

lemma improvedRadius_floor_nnreal :
    ⌊improvedRadius * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = 65541 := by
  norm_num [improvedRadius, IRSProfile.Index]

lemma exists_improved_exact_support
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (γ : IRSProfile.Field)
    (hγ : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
      (improvedRadius : ℝ)) :
    ∃ S : Finset IRSProfile.Index, S.card = 196603 ∧
      LinearCode.projectedWord
          (fun x => ∑ j, AffineLineGenerator IRSProfile.Field γ j • U j x) S ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode S ∧
      ∃ j : Fin 2, LinearCode.projectedWord (U j) S ∉
        LinearCode.projectedCodeSubmod IRSProfile.baseCode S := by
  apply exists_exact_mca_support_rs
    (domain := IRSProfile.domain) (k := IRSProfile.baseDimension)
    (a := 196603) (by norm_num [IRSProfile.baseDimension]) (by
      norm_num [IRSProfile.baseDimension])
  · intro T hT
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor T
        (show (0 : ℝ) ≤ (improvedRadius : ℝ) by positivity)).mp hT
    rw [improvedRadius_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn] at hcomp
    omega
  · simpa [IRSProfile.baseCode] using hγ

noncomputable def improvedSupport
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (γ : IRSProfile.Field) :
    Finset IRSProfile.Index := by
  classical
  exact if hγ : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
        (improvedRadius : ℝ) then
      Classical.choose (exists_improved_exact_support U γ hγ)
    else ∅

lemma improvedSupport_spec
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (γ : IRSProfile.Field)
    (hγ : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
      (improvedRadius : ℝ)) :
    (improvedSupport U γ).card = 196603 ∧
      LinearCode.projectedWord
          (fun x => ∑ j, AffineLineGenerator IRSProfile.Field γ j • U j x)
          (improvedSupport U γ) ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (improvedSupport U γ) ∧
      ∃ j : Fin 2, LinearCode.projectedWord (U j) (improvedSupport U γ) ∉
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (improvedSupport U γ) := by
  rw [improvedSupport, dif_pos hγ]
  exact Classical.choose_spec (exists_improved_exact_support U γ hγ)

lemma puncture_descFactorial_ratio :
    (262144 : ℕ).descFactorial 10 ≤
      5 ^ 10 * (65541 : ℕ).descFactorial 10 := by
  norm_num [Nat.descFactorial]

open Classical in
lemma bad_card_le_of_punctures
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Fintype Γ] [DecidableEq Γ]
    (bad : Γ → Prop) (support : Γ → Finset ι)
    (puncturedBad : (Fin 10 ↪ ι) → Γ → Prop)
    (hn : Fintype.card ι = 262144)
    (hsupport : ∀ γ, bad γ → (support γ).card = 196603)
    (htransfer : ∀ γ e, bad γ → Disjoint (punctureFinset e) (support γ) →
      puncturedBad e γ)
    (hpunctured : ∀ e, (Finset.univ.filter fun γ => puncturedBad e γ).card ≤ 262134) :
    (Finset.univ.filter fun γ => bad γ).card ≤ 5 ^ 10 * 262134 := by
  let B := Finset.univ.filter fun γ => bad γ
  let A := (Finset.univ : Finset (Fin 10 ↪ ι))
  let valid (γ : Γ) (e : Fin 10 ↪ ι) : Prop :=
    Disjoint (punctureFinset e) (support γ)
  have hlower : ∀ γ ∈ B, (65541 : ℕ).descFactorial 10 ≤
      (A.filter fun e => valid γ e).card := by
    intro γ hγB
    have hγ : bad γ := (Finset.mem_filter.mp hγB).2
    simp only [A, valid]
    rw [card_validPunctures, hsupport γ hγ, hn]
  have hupper : ∀ e ∈ A, (B.filter fun γ => valid γ e).card ≤ 262134 := by
    intro e heA
    calc
      (B.filter fun γ => valid γ e).card ≤
          (Finset.univ.filter fun γ => puncturedBad e γ).card := by
        apply Finset.card_le_card
        intro γ hγ
        have hγB : γ ∈ B := (Finset.mem_filter.mp hγ).1
        have hvalid : valid γ e := (Finset.mem_filter.mp hγ).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ γ,
            htransfer γ e (Finset.mem_filter.mp hγB).2 hvalid⟩
      _ ≤ 262134 := hpunctured e
  have hinc := incidence_double_count B A valid
    ((65541 : ℕ).descFactorial 10) 262134 hlower hupper
  have hAcard : A.card = (262144 : ℕ).descFactorial 10 := by
    simp [A, Fintype.card_embedding_eq, hn]
  rw [hAcard] at hinc
  have hchain :
      B.card * (65541 : ℕ).descFactorial 10 ≤
        (5 ^ 10 * 262134) * (65541 : ℕ).descFactorial 10 := by
    calc
      B.card * (65541 : ℕ).descFactorial 10 ≤
          (262144 : ℕ).descFactorial 10 * 262134 := hinc
      _ ≤ (5 ^ 10 * (65541 : ℕ).descFactorial 10) * 262134 :=
        Nat.mul_le_mul_right 262134 puncture_descFactorial_ratio
      _ = (5 ^ 10 * 262134) * (65541 : ℕ).descFactorial 10 := by ring
  have hLpos : 0 < (65541 : ℕ).descFactorial 10 := by
    norm_num [Nat.descFactorial]
  change B.card ≤ 5 ^ 10 * 262134
  exact Nat.le_of_mul_le_mul_right hchain hLpos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
open Classical in
lemma improved_bad_card_le
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) :
    (Finset.univ.filter fun γ : IRSProfile.Field =>
      IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
        (improvedRadius : ℝ)).card ≤ 5 ^ 10 * 262134 := by
  apply bad_card_le_of_punctures
    (bad := fun γ => IsMCA (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode γ U (improvedRadius : ℝ))
    (support := improvedSupport U)
    (puncturedBad := fun e γ =>
      IsMCA (AffineLineGenerator IRSProfile.Field)
        (ReedSolomon.code
          (puncturedDomain IRSProfile.domain (punctureFinset e))
          IRSProfile.baseDimension) γ
        (fun j => restrictWord (punctureFinset e) (U j)) (puncturedRadius : ℝ))
  · norm_num [IRSProfile.Index]
  · intro γ hγ
    exact (improvedSupport_spec U γ hγ).1
  · intro γ e hγ hdis
    have hs := improvedSupport_spec U γ hγ
    apply isMCA_punctured_of_exact_support
      (domain := IRSProfile.domain) (k := IRSProfile.baseDimension)
      (P := punctureFinset e) (S := improvedSupport U γ) hdis
    · rw [hs.1, card_puncturedIndex (punctureFinset e) (card_punctureFinset e)]
      norm_num [puncturedRadius]
    · simpa [IRSProfile.baseCode] using hs.2.1
    · simpa [IRSProfile.baseCode] using hs.2.2
  · intro e
    exact punctured_bad_card_le (punctureFinset e) (card_punctureFinset e)
      (fun j => restrictWord (punctureFinset e) (U j))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
open Classical in
lemma base_mca_improved_le :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (improvedRadius : ℝ) ≤
      ((5 ^ 10 * 262134 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast improved_bad_card_le U

lemma card_offDiag_incident_le (D : Finset (Fin 5)) :
    ((Finset.univ : Finset (Fin 5)).offDiag.filter
      (fun p => p.1 ∈ D ∨ p.2 ∈ D)).card ≤ 6 * D.card + 2 := by
  classical
  let C := (Finset.univ : Finset (Fin 5)) \ D
  have hsub :
      (Finset.univ : Finset (Fin 5)).offDiag.filter
          (fun p => p.1 ∈ D ∨ p.2 ∈ D) ⊆
        D.offDiag ∪ (D ×ˢ C) ∪ (C ×ˢ D) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and, Finset.mem_union, Finset.mem_product] at hp ⊢
    rcases hp with ⟨hne, hpD | hpD⟩
    · by_cases h2D : p.2 ∈ D
      · exact Or.inl (Or.inl ⟨hpD, h2D, hne⟩)
      · exact Or.inl (Or.inr ⟨hpD, by simp [C, h2D]⟩)
    · by_cases h1D : p.1 ∈ D
      · exact Or.inl (Or.inl ⟨h1D, hpD, hne⟩)
      · exact Or.inr ⟨by simp [C, h1D], hpD⟩
  calc
    ((Finset.univ : Finset (Fin 5)).offDiag.filter
      (fun p => p.1 ∈ D ∨ p.2 ∈ D)).card ≤
        (D.offDiag ∪ (D ×ˢ C) ∪ (C ×ˢ D)).card :=
      Finset.card_le_card hsub
    _ ≤ D.offDiag.card + (D ×ˢ C).card + (C ×ˢ D).card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ 6 * D.card + 2 := by
      simp only [Finset.offDiag_card, Finset.card_product, C,
        Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ,
        Fintype.card_fin]
      have hD : D.card ≤ 5 := by simpa using Finset.card_le_univ D
      interval_cases h : D.card <;> norm_num at *

open scoped BigOperators in
lemma sum_card_eq_sum_incidence
    {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Finset ι) :
    (∑ x : κ, (A x).card) =
      ∑ i : ι, ((Finset.univ : Finset κ).filter fun x => i ∈ A x).card := by
  classical
  calc
    (∑ x : κ, (A x).card) =
        ∑ x : κ, ∑ i : ι, if i ∈ A x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      simp
    _ = ∑ i : ι, ∑ x : κ, if i ∈ A x then 1 else 0 := Finset.sum_comm
    _ = ∑ i : ι,
        ((Finset.univ : Finset κ).filter fun x => i ∈ A x).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_boole (R := ℕ) (fun x : κ => i ∈ A x) Finset.univ

open scoped BigOperators in
lemma sum_card_eq_sum_incidence_on
    {κ ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (A : κ → Finset ι) :
    (∑ x ∈ K, (A x).card) =
      ∑ i : ι, (K.filter fun x => i ∈ A x).card := by
  classical
  calc
    (∑ x ∈ K, (A x).card) =
        ∑ x ∈ K, ∑ i : ι, if i ∈ A x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      simp
    _ = ∑ i : ι, ∑ x ∈ K, if i ∈ A x then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι, (K.filter fun x => i ∈ A x).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_boole (R := ℕ) (fun x : κ => i ∈ A x) K

open scoped BigOperators in
lemma no_five_close_words
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (C : Set (ι → A)) (y : ι → A) (c : Fin 5 → ι → A)
    (hc_mem : ∀ j, c j ∈ C) (hc_inj : Function.Injective c)
    (hmin : Code.minDist C = 131073) (hn : Fintype.card ι = 262144)
    (r : ℕ) (hclose : ∀ j, Δ₀(y, c j) ≤ r)
    (hr : 30 * r + 2 * 262144 < 20 * 131073) : False := by
  classical
  let E : Fin 5 → Finset ι := fun j => Code.disagreementCols y (c j)
  let D : ι → Finset (Fin 5) := fun i =>
    Finset.univ.filter fun j => i ∈ E j
  let pairs := (Finset.univ : Finset (Fin 5)).offDiag
  have hEcard (j : Fin 5) : (E j).card ≤ r := by
    simpa [E, Code.hammingDist_eq_disagreementCols_card] using hclose j
  have hcenter : (∑ j : Fin 5, (E j).card) ≤ 5 * r := by
    calc
      (∑ j : Fin 5, (E j).card) ≤ ∑ _j : Fin 5, r :=
        Finset.sum_le_sum fun j _ => hEcard j
      _ = 5 * r := by simp
  have hsumED : (∑ j : Fin 5, (E j).card) = ∑ i : ι, (D i).card := by
    simpa [D] using sum_card_eq_sum_incidence E
  have hpair_min (p : Fin 5 × Fin 5) (hp : p ∈ pairs) :
      131073 ≤ Δ₀(c p.1, c p.2) := by
    have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    rw [← hmin]
    exact Code.minDist_le_dist (hc_mem p.1) (hc_mem p.2) (hc_inj.ne hpne)
  have hpair_union (p : Fin 5 × Fin 5) :
      Δ₀(c p.1, c p.2) ≤ ((E p.1) ∪ (E p.2)).card := by
    rw [Code.hammingDist_eq_disagreementCols_card]
    apply Finset.card_le_card
    intro i hi
    simp only [E, Code.disagreementCols, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union] at hi ⊢
    by_contra h
    push Not at h
    exact hi (h.1.symm.trans h.2)
  have hlower :
      20 * 131073 ≤ ∑ p ∈ pairs, Δ₀(c p.1, c p.2) := by
    calc
      20 * 131073 = ∑ _p ∈ pairs, 131073 := by
        simp [pairs, Finset.offDiag_card]
      _ ≤ ∑ p ∈ pairs, Δ₀(c p.1, c p.2) :=
        Finset.sum_le_sum hpair_min
  have hupper₁ :
      (∑ p ∈ pairs, Δ₀(c p.1, c p.2)) ≤
        ∑ p ∈ pairs, ((E p.1) ∪ (E p.2)).card :=
    Finset.sum_le_sum fun p _ => hpair_union p
  have hunion :
      (∑ p ∈ pairs, ((E p.1) ∪ (E p.2)).card) =
        ∑ i : ι, (pairs.filter fun p => i ∈ E p.1 ∨ i ∈ E p.2).card := by
    simpa only [Finset.mem_union] using
      sum_card_eq_sum_incidence_on pairs (fun p => (E p.1) ∪ (E p.2))
  have hpoint (i : ι) :
      (pairs.filter fun p => i ∈ E p.1 ∨ i ∈ E p.2).card ≤
        6 * (D i).card + 2 := by
    simpa [pairs, D] using card_offDiag_incident_le (D i)
  have hupper₂ :
      (∑ i : ι, (pairs.filter fun p => i ∈ E p.1 ∨ i ∈ E p.2).card) ≤
        6 * (∑ i : ι, (D i).card) + 2 * Fintype.card ι := by
    calc
      (∑ i : ι, (pairs.filter fun p => i ∈ E p.1 ∨ i ∈ E p.2).card) ≤
          ∑ i : ι, (6 * (D i).card + 2) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = 6 * (∑ i : ι, (D i).card) + 2 * Fintype.card ι := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring
  have hfinal : 20 * 131073 ≤ 30 * r + 2 * 262144 := by
    calc
      20 * 131073 ≤ ∑ p ∈ pairs, Δ₀(c p.1, c p.2) := hlower
      _ ≤ ∑ p ∈ pairs, ((E p.1) ∪ (E p.2)).card := hupper₁
      _ = ∑ i : ι, (pairs.filter fun p => i ∈ E p.1 ∨ i ∈ E p.2).card := hunion
      _ ≤ 6 * (∑ i : ι, (D i).card) + 2 * Fintype.card ι := hupper₂
      _ = 6 * (∑ j : Fin 5, (E j).card) + 2 * 262144 := by rw [← hsumED, hn]
      _ ≤ 6 * (5 * r) + 2 * 262144 := Nat.add_le_add_right
        (Nat.mul_le_mul_left 6 hcenter) _
      _ = 30 * r + 2 * 262144 := by ring
  omega

noncomputable abbrev ImprovedSquaredCode :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem improvedSquaredCode_minDistance :
    Code.minDist ImprovedSquaredCode = 131073 := by
  calc
    Code.minDist ImprovedSquaredCode =
      Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance


lemma nnrat_le_nnreal_of_coe_le {x : ℚ≥0} {y : ℝ≥0}
    (h : (x : ℝ) ≤ (y : ℝ)) : (x : ℝ≥0) ≤ y := by
  exact_mod_cast h

lemma hammingDist_le_of_mem_close
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq A]
    {C : Set (ι → A)} {y c : ι → A} {δ : ℝ≥0} {r : ℕ}
    (h : c ∈ Code.closeCodewordsRel C y (δ : ℝ))
    (hfloor : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ = r) :
    Δ₀(y, c) ≤ r := by
  have hdR := (Code.mem_closeCodewordsRel_iff.mp h).2
  have hdNN : (δᵣ(y, c) : ℝ≥0) ≤ δ :=
    nnrat_le_nnreal_of_coe_le hdR
  rw [Code.pairRelDist_le_iff_pairDist_le, hfloor] at hdNN
  exact hdNN
set_option maxRecDepth 100000 in
lemma improved_lambda_le_four :
    Code.Lambda ImprovedSquaredCode (improvedRadius : ℝ) ≤ (4 : ℕ∞) := by
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
      (hT (c j) (hBT (e j).2)) improvedRadius_floor_nnreal
  · norm_num

lemma mca_improved_le :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (improvedRadius : ℝ) ≤
      ((5 ^ 10 * 262134 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (improvedRadius : ℝ) ≤
      mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (improvedRadius : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving improvedRadius
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [improvedRadius]) (by norm_num [improvedRadius]))
    _ ≤ _ := base_mca_improved_le

lemma nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

theorem certifiedGammaError_improved_le :
    certifiedGammaError IRSProfile.code improvedRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  have hLambdaNat :
      (Code.Lambda ImprovedSquaredCode (improvedRadius : ℝ)).toNat ≤ 4 :=
    ENat.toNat_le_of_le_coe improved_lambda_le_four
  have hList :
      ((Code.Lambda ImprovedSquaredCode (improvedRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (improvedRadius : ℝ) +
        ((Code.Lambda
          ((IRSProfile.code ^⋈ (Fin 2) :
            ModuleCode IRSProfile.Index IRSProfile.Field
              (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
            Set (IRSProfile.Index →
              Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
          (improvedRadius : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      ((5 ^ 10 * 262134 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      apply add_le_add mca_improved_le
      simpa [ImprovedSquaredCode] using hList
    _ = ((5 ^ 10 * 262134 + 4 : ℕ) : ENNReal) /
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
end Puncture

end ProximityPrize.SubmissionLower
