import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.BelowHalf

open Polynomial
open scoped BigOperators

abbrev F := ProximityPrize.Benchmark.IRSProfile.Field
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev d := ProximityPrize.Benchmark.IRSProfile.baseDimension
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving

/-- The leading `c + 1` terms of a monic degree-`khat` vanishing polynomial. -/
noncomputable def leadingPart {K : Type} [CommRing K]
    (khat c : Nat) (lam : Nat → K) : Polynomial K :=
  ∑ i ∈ Finset.range (c + 1),
    Polynomial.C ((-1) ^ i * lam i) *
      (Polynomial.X : Polynomial K) ^ (khat - i)

/-- Vieta decomposition after fixing the first `c` elementary symmetric sums. -/
theorem prod_X_sub_C_eq_leadingPart_add_remainder
    {K J : Type} [CommRing K] {S : Finset J} {khat c : Nat} {lam : Nat → K}
    (points : J → K) (hcard : S.card = khat) (hck : c ≤ khat)
    (hesymm : ∀ i ≤ c, (S.1.map points).esymm i = lam i) :
    ∃ p : Polynomial K, p.degree ≤ ((khat - c - 1 : Nat) : WithBot Nat) ∧
      ∏ j ∈ S, ((Polynomial.X : Polynomial K) -
        Polynomial.C (points j)) =
        leadingPart khat c lam + p := by
  classical
  subst hcard
  have hV : ∏ j ∈ S,
      ((Polynomial.X : Polynomial K) - Polynomial.C (points j)) =
      ∑ j ∈ Finset.range (S.card + 1),
        Polynomial.C ((-1) ^ j *
          (S.1.map points).esymm j) *
          (Polynomial.X : Polynomial K) ^ (S.card - j) := by
    rw [Finset.prod_eq_multiset_prod]
    have hmap :
        S.1.map (fun j => (Polynomial.X : Polynomial K) - Polynomial.C (points j)) =
        (S.1.map points).map
          (fun t => (Polynomial.X : Polynomial K) - Polynomial.C t) := by
      rw [Multiset.map_map]
      rfl
    rw [hmap]
    rw [Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul, map_pow, map_neg, map_one, mul_assoc]
      rfl
  have hsplit : ∑ j ∈ Finset.range (S.card + 1),
      Polynomial.C ((-1) ^ j *
        (S.1.map points).esymm j) *
        (Polynomial.X : Polynomial K) ^ (S.card - j) =
      (∑ j ∈ Finset.range (c + 1),
        Polynomial.C ((-1) ^ j *
          (S.1.map points).esymm j) *
          (Polynomial.X : Polynomial K) ^ (S.card - j)) +
      ∑ j ∈ Finset.Ico (c + 1) (S.card + 1),
        Polynomial.C ((-1) ^ j *
          (S.1.map points).esymm j) *
          (Polynomial.X : Polynomial K) ^ (S.card - j) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (c + 1)) (by omega)]
  refine ⟨∑ j ∈ Finset.Ico (c + 1) (S.card + 1),
      Polynomial.C ((-1) ^ j *
        (S.1.map points).esymm j) *
        (Polynomial.X : Polynomial K) ^ (S.card - j), ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans ?_
    have hj' := Finset.mem_Ico.mp hj
    have hle : S.card - j ≤ S.card - c - 1 := by omega
    exact_mod_cast hle
  · rw [hV, hsplit, leadingPart]
    apply congrArg (fun q => q + ∑ j ∈ Finset.Ico (c + 1) (S.card + 1),
      Polynomial.C ((-1) ^ j *
        (S.1.map points).esymm j) *
        (Polynomial.X : Polynomial K) ^ (S.card - j))
    exact Finset.sum_congr rfl fun i hi => by
      rw [hesymm i (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem field_card_lt_two_pow_186 : Fintype.card F < 2 ^ 186 := by
  change Fintype.card KoalaBear.Ext6 < 2 ^ 186
  rw [KoalaBear.card_ext6]
  norm_num [KoalaBear.fieldSize]

private def qBound : Nat := 2 ^ 186

private theorem qBound_eq : qBound = 2 ^ 186 := rfl

private theorem field_card_lt_qBound : Fintype.card F < qBound := by
  rw [qBound_eq]
  exact field_card_lt_two_pow_186

theorem two_pow_191022_lt_centralBinom_96000 :
    2 ^ 191022 < Nat.choose 192000 96000 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 96000 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hle : Nat.choose 192000 96000 ≤ 2 ^ 191022 := Nat.le_of_not_gt hnot
  have hbad : 4 ^ 96000 < 96000 * 2 ^ 191022 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 96000 hle)
  have hreverse : 96000 * 2 ^ 191022 < 4 ^ 96000 := by
    calc
      96000 * 2 ^ 191022 < 2 ^ 17 * 2 ^ 191022 := by gcongr <;> norm_num
      _ = 2 ^ (17 + 191022) := (pow_add 2 17 191022).symm
      _ < 2 ^ (2 * 96000) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = (2 ^ 2) ^ 96000 := pow_mul 2 2 96000
      _ = 4 ^ 96000 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem two_pow_191022_lt_choose (c : Nat) (hc : c ≤ 1024) :
    2 ^ 191022 < Nat.choose 262144 (131072 + c) := by
  have hc' : c ≤ 131072 := by omega
  rw [← Nat.choose_symm (show 131072 + c ≤ 262144 by omega)]
  have hsub : 262144 - (131072 + c) = 131072 - c := by omega
  rw [hsub]
  have hmono : Nat.centralBinom 96000 ≤ Nat.centralBinom (131072 - c) :=
    Nat.centralBinom_strictMono.monotone (by omega)
  rw [Nat.centralBinom_eq_two_mul_choose,
    Nat.centralBinom_eq_two_mul_choose] at hmono
  have hlargeN : 2 * (131072 - c) ≤ 262144 := by omega
  exact two_pow_191022_lt_centralBinom_96000.trans_le
    (hmono.trans (Nat.choose_le_choose (131072 - c) hlargeN))

theorem field_pow_le_1024 (c : Nat) (hc : c ≤ 1024) :
    Fintype.card F ^ c ≤ qBound ^ 1024 := by
  have hqpos : 0 < qBound := by
    rw [qBound_eq]
    positivity
  calc
    Fintype.card F ^ c ≤ qBound ^ c :=
      Nat.pow_le_pow_left field_card_lt_qBound.le c
    _ ≤ qBound ^ c * qBound ^ (1024 - c) := by
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hqpos)
    _ = qBound ^ 1024 := by
      rw [← pow_add]
      congr
      omega

theorem field_sub_one_sq_lt :
    (Fintype.card F - 1) ^ 2 < qBound ^ 2 := by
  have h : Fintype.card F - 1 < qBound :=
    lt_of_le_of_lt (Nat.sub_le _ _) field_card_lt_qBound
  rw [pow_two, pow_two]
  apply Nat.mul_lt_mul_of_le_of_lt h.le h
  rw [qBound_eq]
  positivity

private theorem qBound_product_lt_two_pow_191022 :
    qBound ^ 1024 * qBound ^ 2 < 2 ^ 191022 := by
  calc
    qBound ^ 1024 * qBound ^ 2 = 2 ^ (186 * 1024 + 186 * 2) := by
      rw [qBound_eq, ← pow_mul, ← pow_mul, ← pow_add]
    _ < 2 ^ 191022 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : Nat))).2 (by norm_num)

theorem signature_product_lt_two_pow_191022 (c : Nat) (hc : c ≤ 1024) :
    Fintype.card F ^ c * (Fintype.card F - 1) ^ 2 < 2 ^ 191022 := by
  have hqpos : 0 < qBound := by
    rw [qBound_eq]
    positivity
  exact (Nat.mul_lt_mul_of_le_of_lt (field_pow_le_1024 c hc)
    field_sub_one_sq_lt (Nat.pow_pos hqpos)).trans qBound_product_lt_two_pow_191022

theorem signature_space_mul_collision_lt_choose (c : Nat) (hc : c ≤ 1024) :
    Fintype.card (Fin c → F) * (Fintype.card F - 1) ^ 2 <
      Nat.choose 262144 (131072 + c) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  exact (signature_product_lt_two_pow_191022 c hc).trans
    (two_pow_191022_lt_choose c hc)

open ToyProblem
open scoped NNReal

/-- The collision attack restricted to any sufficiently large family of interpolation sets. -/
theorem winningSetSoundness_eq_one_of_interpolation_family
    {ι B K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [Fintype B] [DecidableEq B] [AddCommGroup B] [Module K B]
    {messageLength m z : Nat}
    (enc : (Fin messageLength → K) →ₗ[K] (ι → B)) (δ : ℝ≥0)
    (hlower : ((z - 1 : Nat) : Real) <
      (1 - (δ : Real)) * Fintype.card ι)
    (hupper : (1 - (δ : Real)) * Fintype.card ι ≤ (m : Real))
    (A : Finset (Set.powersetCard ι m))
    (hlarge : (Fintype.card K - 1) ^ 2 < A.card)
    (f : ι → B)
    (hinterpolate : ∀ T ∈ A,
      ∃ u : Fin messageLength → K, ∀ i ∈ (T : Finset ι), f i = enc u i)
    (hfar : ∀ (u : Fin messageLength → K) (S : Finset ι), m < S.card →
      (∀ i ∈ S, f i = enc u i) → False)
    (hzero : ∀ (u : Fin messageLength → K) (S : Finset ι), z ≤ S.card →
      (∀ i ∈ S, enc u i = 0) → u = 0) :
    winningSetDensity enc δ = 1 := by
  classical
  let p : A → Fin messageLength → K := fun T =>
    Classical.choose (hinterpolate T T.property)
  have hp_spec (T : A) :
      ∀ i ∈ ((T : Set.powersetCard ι m) : Finset ι), f i = enc (p T) i :=
    Classical.choose_spec (hinterpolate T T.property)
  have hp : Function.Injective p := by
    intro S T hpST
    apply Subtype.ext
    by_contra hST
    have hcardUnion : m <
        (((S : Set.powersetCard ι m) : Finset ι) ∪
          ((T : Set.powersetCard ι m) : Finset ι)).card := by
      have hsets : (S : Set.powersetCard ι m) ≠ (T : Set.powersetCard ι m) := by
        exact hST
      obtain ⟨i, hiS, hiT⟩ :=
        (Set.powersetCard.exists_mem_notMem_iff_ne
          (S : Set.powersetCard ι m) (T : Set.powersetCard ι m)).mp hsets
      have hTsub : ((T : Set.powersetCard ι m) : Finset ι) ⊆
          ((S : Set.powersetCard ι m) : Finset ι) ∪
            ((T : Set.powersetCard ι m) : Finset ι) := Finset.subset_union_right
      have hTstrict : ((T : Set.powersetCard ι m) : Finset ι) ⊂
          ((S : Set.powersetCard ι m) : Finset ι) ∪
            ((T : Set.powersetCard ι m) : Finset ι) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, ?_⟩
        intro heq
        have hiUnion : i ∈
            ((S : Set.powersetCard ι m) : Finset ι) ∪
              ((T : Set.powersetCard ι m) : Finset ι) :=
          Finset.mem_union_left _ hiS
        have : i ∈ ((T : Set.powersetCard ι m) : Finset ι) := by
          rwa [← heq] at hiUnion
        exact hiT this
      have hlt := Finset.card_lt_card hTstrict
      simpa only [Set.powersetCard.card_eq (T : Set.powersetCard ι m)] using hlt
    apply hfar (p S)
      (((S : Set.powersetCard ι m) : Finset ι) ∪
        ((T : Set.powersetCard ι m) : Finset ι)) hcardUnion
    intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · exact hp_spec S i hiS
    · rw [hpST]
      exact hp_spec T i hiT
  apply HalfRadiusCollision.winningSetSoundness_eq_one_of_large_fixed_word_list
    (m := m) (z := z) enc δ hlower hupper (J := A) p
    (fun T => ((T : Set.powersetCard ι m) : Finset ι)) f hp
  · simpa only [Fintype.card_coe] using hlarge
  · exact fun T => Set.powersetCard.card_eq (T : Set.powersetCard ι m)
  · exact hp_spec
  · exact hzero

namespace IRSProfile

open ProximityPrize.Benchmark
open ToyProblem ToyProblem.Impl.IRS

local instance : NeZero s := ⟨by
  norm_num [s, Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = d :=
  Benchmark.IRSProfile.totalDimension_div_interleaving

/-- All column sets on which a word will agree with a codeword. -/
abbrev ColumnSets (c : Nat) := Set.powersetCard I (d + c)

noncomputable instance (c : Nat) : Fintype (ColumnSets c) := Fintype.ofFinite _

theorem card_columnSets (c : Nat) :
    Fintype.card (ColumnSets c) = Nat.choose 262144 (131072 + c) := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  norm_num [I, d, Benchmark.IRSProfile.Index, Benchmark.IRSProfile.baseDimension]

/-- The first `c` nonconstant Vieta coefficients of a column set. -/
noncomputable def signature (c : Nat) (T : ColumnSets c) : Fin c → F :=
  fun i => ((T : Finset I).1.map Benchmark.IRSProfile.domain).esymm (i + 1)

/-- A largest signature fiber contains enough colliding codewords for the attack. -/
theorem exists_large_signature_fiber (c : Nat) (hc : c ≤ 1024) :
    ∃ a : Fin c → F,
      (Fintype.card F - 1) ^ 2 <
        (Finset.univ.filter fun T : ColumnSets c => signature c T = a).card := by
  classical
  by_contra hno
  push_neg at hno
  have hsum : Fintype.card (ColumnSets c) =
      ∑ a : Fin c → F,
        (Finset.univ.filter fun T : ColumnSets c => signature c T = a).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ColumnSets c)))
      (t := (Finset.univ : Finset (Fin c → F))) (f := signature c)
      (fun _ _ => Finset.mem_univ _))
  have hle : Fintype.card (ColumnSets c) ≤
      Fintype.card (Fin c → F) * (Fintype.card F - 1) ^ 2 := by
    rw [hsum]
    calc
      (∑ a : Fin c → F,
          (Finset.univ.filter fun T : ColumnSets c => signature c T = a).card) ≤
          ∑ _a : Fin c → F, (Fintype.card F - 1) ^ 2 := by
            apply Finset.sum_le_sum
            intro a _
            exact hno a
      _ = Fintype.card (Fin c → F) * (Fintype.card F - 1) ^ 2 := by simp
  have hlt : Fintype.card (Fin c → F) * (Fintype.card F - 1) ^ 2 <
      Fintype.card (ColumnSets c) := by
    rw [card_columnSets]
    exact signature_space_mul_collision_lt_choose c hc
  omega

noncomputable def vanishing {c : Nat} (T : ColumnSets c) : Polynomial F :=
  ∏ j ∈ (T : Finset I),
    ((Polynomial.X : Polynomial F) - Polynomial.C (Benchmark.IRSProfile.domain j))

/-- Two sets with the same signature have vanishing polynomials whose difference
has degree below the base Reed--Solomon dimension. -/
theorem vanishing_sub_degree_lt {c : Nat} (hcpos : 0 < c)
    {S T : ColumnSets c} (hsig : signature c S = signature c T) :
    (vanishing S - vanishing T).degree < (d : WithBot Nat) := by
  classical
  let lam : Nat → F := fun i =>
    (((T : Finset I).1.map Benchmark.IRSProfile.domain).esymm i)
  have hsymm (U : ColumnSets c) (hU : signature c U = signature c T) :
      ∀ i ≤ c,
        (((U : Finset I).1.map Benchmark.IRSProfile.domain).esymm i) = lam i := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [lam, Multiset.esymm]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hj : j < c := by omega
      exact congrFun hU ⟨j, hj⟩
  obtain ⟨pS, hpS, hS⟩ := prod_X_sub_C_eq_leadingPart_add_remainder
    Benchmark.IRSProfile.domain (Set.powersetCard.card_eq S)
    (show c ≤ d + c by omega) (hsymm S hsig)
  obtain ⟨pT, hpT, hT⟩ := prod_X_sub_C_eq_leadingPart_add_remainder
    Benchmark.IRSProfile.domain (Set.powersetCard.card_eq T)
    (show c ≤ d + c by omega) (hsymm T rfl)
  have hdeg : (pS - pT).degree ≤ ((d - 1 : Nat) : WithBot Nat) := by
    refine (Polynomial.degree_sub_le pS pT).trans ?_
    simp only [sup_le_iff]
    constructor
    · simpa [d] using hpS
    · simpa [d] using hpT
  rw [vanishing, vanishing, hS, hT]
  have heq : leadingPart (d + c) c lam + pS -
      (leadingPart (d + c) c lam + pT) = pS - pT := by ring
  rw [heq]
  exact hdeg.trans_lt (by
    exact_mod_cast (show d - 1 < d by
      norm_num [d, Benchmark.IRSProfile.baseDimension]))

noncomputable def vanishingWord {c : Nat} (T : ColumnSets c) : I → Fin s → F :=
  fun j row => if row = 0 then (vanishing T).eval (Benchmark.IRSProfile.domain j) else 0

theorem exists_message_agree {c : Nat} (hcpos : 0 < c)
    (T₀ T : ColumnSets c) (hsig : signature c T = signature c T₀) :
    ∃ u : Fin k → F, ∀ j ∈ (T : Finset I),
      vanishingWord T₀ j = Benchmark.IRSProfile.encoder u j := by
  classical
  let p : Polynomial F := vanishing T₀ - vanishing T
  have hpdeg : p.degree < (k / s : Nat) := by
    rw [rowDimension_eq]
    exact vanishing_sub_degree_lt hcpos hsig.symm
  have hpmem : p ∈ Polynomial.degreeLT F (k / s) :=
    Polynomial.mem_degreeLT.mpr hpdeg
  let coeff : Fin (k / s) → F :=
    Polynomial.degreeLTEquiv F (k / s) ⟨p, hpmem⟩
  let rows : Fin s → Fin (k / s) → F :=
    fun row => if row = 0 then coeff else 0
  let u : Fin k → F := flatten k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension rows
  have hpoly : ToyProblem.Spec.rsPolynomial (k / s) coeff = p := by
    exact congrArg Subtype.val
      ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply ⟨p, hpmem⟩)
  refine ⟨u, ?_⟩
  intro j hj
  funext row
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change vanishingWord T₀ j row = ToyProblem.Spec.rsEncoder (k / s)
    Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
        (flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension rows) row) j
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows 0 = coeff by simp [rows], ToyProblem.Spec.rsEncoder_apply, hpoly]
    have hroot : (vanishing T).eval (Benchmark.IRSProfile.domain j) = 0 := by
      rw [vanishing, eval_prod]
      exact Finset.prod_eq_zero hj (by simp)
    simp [vanishingWord, p, hroot]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [vanishingWord, rows, hrow] using hz.symm

theorem no_message_agrees_on_more_than {c : Nat} (hcpos : 0 < c)
    (T₀ : ColumnSets c) (u : Fin k → F) (S : Finset I)
    (hcard : d + c < S.card)
    (hagree : ∀ j ∈ S,
      vanishingWord T₀ j = Benchmark.IRSProfile.encoder u j) : False := by
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (d : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hVdeg : (vanishing T₀).degree = ((d + c : Nat) : WithBot Nat) := by
    rw [vanishing, Polynomial.degree_prod]
    simp [Polynomial.degree_X_sub_C, Set.powersetCard.card_eq T₀]
  have hVdegS : (vanishing T₀).degree < (S.card : Nat) := by
    rw [hVdeg]
    exact_mod_cast hcard
  have hqdegS : q.degree < (S.card : Nat) := by
    exact hqdeg.trans (by exact_mod_cast (show d < S.card by omega))
  have heval : ∀ j ∈ S,
      (vanishing T₀).eval (Benchmark.IRSProfile.domain j) =
        q.eval (Benchmark.IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin s)
    rw [Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at h
    simpa [vanishingWord, q] using h
  have heq : vanishing T₀ = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      S Benchmark.IRSProfile.domain.injective.injOn hVdegS hqdegS heval
  have hbad : (((d + c : Nat) : WithBot Nat)) < (d : Nat) := by
    rw [← hVdeg, heq]
    exact hqdeg
  exact (not_lt_of_ge (by exact_mod_cast (show d ≤ d + c by omega))) hbad

theorem message_eq_zero_of_zero_on_many {c : Nat}
    (u : Fin k → F) (S : Finset I) (hcard : d + c ≤ S.card)
    (hzero : ∀ j ∈ S, Benchmark.IRSProfile.encoder u j = 0) : u = 0 := by
  have hdcard : d ≤ S.card := by omega
  have hu := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := u) hdcard hzero
  have hz := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := (0 : Fin k → F)) hdcard (by
      intro j hj
      exact congrFun (map_zero Benchmark.IRSProfile.encoder) j)
  rw [← hu, hz]

/-- Soundness is maximal throughout the grid cell corresponding to agreement on
`d + c` columns, for each `1 ≤ c ≤ 1024`. -/
theorem winningSetSoundness_eq_one_cell (c : Nat) (hcpos : 0 < c) (hc : c ≤ 1024)
    (δ : ℝ≥0)
    (hlower : (((d + c) - 1 : Nat) : Real) <
      (1 - (δ : Real)) * Fintype.card I)
    (hupper : (1 - (δ : Real)) * Fintype.card I ≤ ((d + c : Nat) : Real)) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_large_signature_fiber c hc
  let A : Finset (ColumnSets c) :=
    Finset.univ.filter fun T : ColumnSets c => signature c T = a
  have hAcard : (Fintype.card F - 1) ^ 2 < A.card := by
    simpa only [A] using ha
  have hApos : 0 < A.card := lt_of_le_of_lt (Nat.zero_le _) hAcard
  obtain ⟨T₀, hT₀⟩ := Finset.card_pos.mp hApos
  apply winningSetSoundness_eq_one_of_interpolation_family
    (K := F) (ι := I) (B := Fin s → F) (messageLength := k) (m := d + c)
    Benchmark.IRSProfile.encoder δ hlower hupper A hAcard (vanishingWord T₀)
  · intro T hT
    have hsigT : signature c T = a := (Finset.mem_filter.mp hT).2
    have hsigT₀ : signature c T₀ = a := (Finset.mem_filter.mp hT₀).2
    exact exists_message_agree hcpos T₀ T (hsigT.trans hsigT₀.symm)
  · intro u S hcard hagree
    exact no_message_agrees_on_more_than hcpos T₀ u S hcard hagree
  · intro u S hcard hzero
    exact message_eq_zero_of_zero_on_many u S hcard hzero

theorem winningSetSoundness_eq_one_cell_interval
    (c : Nat) (hcpos : 0 < c) (hc : c ≤ 1024) (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico
      ((((131072 - c : Nat) : Nat) : ℝ≥0) / 262144)
      ((((131073 - c : Nat) : Nat) : ℝ≥0) / 262144)) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  apply winningSetSoundness_eq_one_cell c hcpos hc δ
  · have hlt : (δ : Real) < ((131073 - c : Nat) : Real) / 262144 := by
      exact_mod_cast hδ.2
    norm_num [d, I, Benchmark.IRSProfile.baseDimension,
      Benchmark.IRSProfile.Index] at hlt ⊢
    rw [Nat.cast_sub (by omega : c ≤ 131073)] at hlt
    nlinarith
  · have hge : ((131072 - c : Nat) : Real) / 262144 ≤ (δ : Real) := by
      exact_mod_cast hδ.1
    norm_num [d, I, Benchmark.IRSProfile.baseDimension,
      Benchmark.IRSProfile.Index] at hge ⊢
    rw [Nat.cast_sub (by omega : c ≤ 131072)] at hge
    nlinarith

/-- A single large signature fiber certifies the whole suffix beginning at grid
index `130048`.  The interpolation sets have `d + 1024` columns, while the
zero-codeword uniqueness argument only needs `d` columns. -/
theorem winningSetSoundness_eq_one_suffix (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico
      (ProximityGap.gridPt (ι := I) 130048)
      Benchmark.IRSProfile.minRelativeDistance) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_large_signature_fiber 1024 (by norm_num)
  let A : Finset (ColumnSets 1024) :=
    Finset.univ.filter fun T : ColumnSets 1024 => signature 1024 T = a
  have hAcard : (Fintype.card F - 1) ^ 2 < A.card := by
    simpa only [A] using ha
  have hApos : 0 < A.card := lt_of_le_of_lt (Nat.zero_le _) hAcard
  obtain ⟨T₀, hT₀⟩ := Finset.card_pos.mp hApos
  apply winningSetSoundness_eq_one_of_interpolation_family
    (K := F) (ι := I) (B := Fin s → F) (messageLength := k)
    (m := d + 1024) (z := d) Benchmark.IRSProfile.encoder δ
    (A := A) (f := vanishingWord T₀)
  · have hlt : (δ : Real) < (131073 : Real) / 262144 := by
      exact_mod_cast hδ.2
    norm_num [d, I, Benchmark.IRSProfile.minRelativeDistance,
      Benchmark.IRSProfile.baseDimension, Benchmark.IRSProfile.Index] at hlt ⊢
    linarith
  · have hgeGrid :
        ((ProximityGap.gridPt (ι := I) 130048 : ℝ≥0) : Real) ≤ (δ : Real) := by
      exact_mod_cast hδ.1
    have hge : (130048 : Real) / 262144 ≤ (δ : Real) := by
      norm_num [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index] at hgeGrid ⊢
      exact hgeGrid
    norm_num [d, I, Benchmark.IRSProfile.baseDimension,
      Benchmark.IRSProfile.Index] at hge ⊢
    linarith
  · exact hAcard
  · intro T hT
    have hsigT : signature 1024 T = a := (Finset.mem_filter.mp hT).2
    have hsigT₀ : signature 1024 T₀ = a := (Finset.mem_filter.mp hT₀).2
    exact exists_message_agree (by norm_num) T₀ T (hsigT.trans hsigT₀.symm)
  · intro u S hcard hagree
    exact no_message_agrees_on_more_than (by norm_num) T₀ u S hcard hagree
  · intro u S hcard hzero
    exact message_eq_zero_of_zero_on_many (c := 0) u S (by simpa using hcard) hzero

theorem winningSetSoundness_eq_one_below_half (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico ((131057 : ℝ≥0) / 262144) (1 / 2 : ℝ≥0)) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  by_cases h58 : δ < (131058 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 15 (by norm_num) (by norm_num) δ
    simpa using And.intro hδ.1 h58
  by_cases h59 : δ < (131059 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 14 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h58) h59
  by_cases h60 : δ < (131060 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 13 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h59) h60
  by_cases h61 : δ < (131061 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 12 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h60) h61
  by_cases h62 : δ < (131062 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 11 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h61) h62
  by_cases h63 : δ < (131063 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 10 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h62) h63
  by_cases h64 : δ < (131064 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 9 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h63) h64
  by_cases h65 : δ < (131065 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 8 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h64) h65
  by_cases h66 : δ < (131066 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 7 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h65) h66
  by_cases h67 : δ < (131067 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 6 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h66) h67
  by_cases h68 : δ < (131068 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 5 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h67) h68
  by_cases h69 : δ < (131069 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 4 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h68) h69
  by_cases h70 : δ < (131070 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 3 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h69) h70
  by_cases h71 : δ < (131071 : ℝ≥0) / 262144
  · apply winningSetSoundness_eq_one_cell_interval 2 (by norm_num) (by norm_num) δ
    simpa using And.intro (le_of_not_gt h70) h71
  · apply winningSetSoundness_eq_one_cell_interval 1 (by norm_num) (by norm_num) δ
    have hhalf : (1 / 2 : ℝ≥0) = (131072 : ℝ≥0) / 262144 := by norm_num
    simpa [hhalf] using And.intro (le_of_not_gt h71) hδ.2

end IRSProfile

end ProximityPrize.SubmissionUpper.BelowHalf
