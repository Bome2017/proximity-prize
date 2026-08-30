import ProximityPrize.SubmissionLower.K

namespace ProximityPrize.SubmissionLower.RFreeJetCodimension

open scoped BigOperators
open ContactInterpolation ContactTranslation ContactRankKernel

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

private theorem shifted_power_dvd_iff_taylor_coeff_zero
    (P : Polynomial K) (x : K) (h : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ h ∣ P ↔
      ∀ j < h, (Polynomial.taylor x P).coeff j = 0 := by
  have hshift : Polynomial.taylor x
      ((Polynomial.X - Polynomial.C x) ^ h) =
      (Polynomial.X : Polynomial K) ^ h := by
    rw [Polynomial.taylor_pow, map_sub, Polynomial.taylor_X,
      Polynomial.taylor_C, add_sub_cancel_right]
  calc
    (Polynomial.X - Polynomial.C x) ^ h ∣ P ↔
        (Polynomial.taylorEquiv x)
            ((Polynomial.X - Polynomial.C x) ^ h) ∣
          (Polynomial.taylorEquiv x) P :=
      (map_dvd_iff (Polynomial.taylorEquiv x)).symm
    _ ↔ (Polynomial.X : Polynomial K) ^ h ∣
        Polynomial.taylor x P := by
      change Polynomial.taylor x
          ((Polynomial.X - Polynomial.C x) ^ h) ∣
        Polynomial.taylor x P ↔ _
      rw [hshift]
    _ ↔ ∀ j < h, (Polynomial.taylor x P).coeff j = 0 :=
      Polynomial.X_pow_dvd_iff

private theorem sum_rootMultiplicity_le_natDegree
    (P : Polynomial K) (points : Finset K) :
    (∑ x ∈ points, P.rootMultiplicity x) ≤ P.natDegree := by
  classical
  have hselected :
      (∑ x ∈ points, Multiset.count x P.roots) ≤ P.roots.card := by
    let all := points ∪ P.roots.toFinset
    calc
      (∑ x ∈ points, Multiset.count x P.roots) ≤
          ∑ x ∈ all, Multiset.count x P.roots := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              Finset.subset_union_left
            simp
      _ = ∑ x ∈ P.roots.toFinset, Multiset.count x P.roots := by
            symm
            apply Finset.sum_subset Finset.subset_union_right
            intro x _ hx
            exact Multiset.count_eq_zero.mpr (by simpa using hx)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  calc
    (∑ x ∈ points, P.rootMultiplicity x) =
        ∑ x ∈ points, Multiset.count x P.roots := by
          apply Finset.sum_congr rfl
          intro x _
          exact (Polynomial.count_roots P).symm
    _ ≤ P.roots.card := hselected
    _ ≤ P.natDegree := Polynomial.card_roots' P

private theorem finrank_degreeLT (q : ℕ) :
    Module.finrank K (Polynomial.degreeLT K q) = q := by
  simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K q)

abbrev JetTarget (points : Finset K) (h : K → ℕ) :=
  (x : points) → Fin (h x) → K

def hermiteJet (q : ℕ) (points : Finset K) (h : K → ℕ) :
    Polynomial.degreeLT K q →ₗ[K] JetTarget points h where
  toFun P x r := (Polynomial.taylor (x : K) (P : Polynomial K)).coeff r
  map_add' P Q := by
    funext x r
    simp
  map_smul' a P := by
    funext x r
    simp

theorem hermiteJet_injective
    (q : ℕ) (points : Finset K) (h : K → ℕ)
    (hq : q ≤ ∑ x ∈ points, h x) :
    Function.Injective (hermiteJet q points h) := by
  intro P Q hPQ
  apply Subtype.ext
  let R : Polynomial K := (P : Polynomial K) - (Q : Polynomial K)
  have hRdegree : R.degree < (q : WithBot ℕ) := by
    apply (Polynomial.degree_sub_le _ _).trans_lt
    exact max_lt
      (Polynomial.mem_degreeLT.mp P.property)
      (Polynomial.mem_degreeLT.mp Q.property)
  have hcoeff : ∀ x ∈ points, ∀ j < h x,
      (Polynomial.taylor x R).coeff j = 0 := by
    intro x hx j hj
    have heq := congrFun (congrFun hPQ ⟨x, hx⟩) ⟨j, hj⟩
    change (Polynomial.taylor x (P : Polynomial K)).coeff j =
      (Polynomial.taylor x (Q : Polynomial K)).coeff j at heq
    simp only [R, map_sub, Polynomial.coeff_sub, heq, sub_self]
  by_contra hne
  have hRne : R ≠ 0 := by
    exact sub_ne_zero.mpr hne
  have hmult : ∀ x ∈ points,
      h x ≤ R.rootMultiplicity x := by
    intro x hx
    apply (Polynomial.le_rootMultiplicity_iff hRne).mpr
    exact (shifted_power_dvd_iff_taylor_coeff_zero R x (h x)).mpr
      (hcoeff x hx)
  have hsum : (∑ x ∈ points, h x) ≤ R.natDegree := by
    calc
      (∑ x ∈ points, h x) ≤
          ∑ x ∈ points, R.rootMultiplicity x := by
            exact Finset.sum_le_sum fun x hx => hmult x hx
      _ ≤ R.natDegree := sum_rootMultiplicity_le_natDegree R points
  have hnat : R.natDegree < q := by
    exact (Polynomial.natDegree_lt_iff_degree_lt hRne).mpr hRdegree
  omega

def repeatedHermiteJet (q L : ℕ) (points : Finset K) (h : K → ℕ) :
    (Fin (L + 1) → Polynomial.degreeLT K q) →ₗ[K]
      (Fin (L + 1) → JetTarget points h) where
  toFun P z := hermiteJet q points h (P z)
  map_add' P Q := by
    funext z
    exact map_add (hermiteJet q points h) (P z) (Q z)
  map_smul' a P := by
    funext z
    exact map_smul (hermiteJet q points h) a (P z)

theorem repeatedHermiteJet_injective
    (q L : ℕ) (points : Finset K) (h : K → ℕ)
    (hq : q ≤ ∑ x ∈ points, h x) :
    Function.Injective (repeatedHermiteJet q L points h) := by
  intro P Q hPQ
  funext z
  apply hermiteJet_injective q points h hq
  exact congrFun hPQ z

theorem piLinearMap_injective_of_upperTriangular
    {n : ℕ} {S T : Fin n → Type*}
    [∀ i, AddCommGroup (S i)] [∀ i, Module K (S i)]
    [∀ i, AddCommGroup (T i)] [∀ i, Module K (T i)]
    (F : ((i : Fin n) → S i) →ₗ[K] ((i : Fin n) → T i))
    (diagonal : (i : Fin n) → S i →ₗ[K] T i)
    (hdiagonal : ∀ i, Function.Injective (diagonal i))
    (hupper : ∀ P i, (∀ j, i < j → P j = 0) →
      F P i = diagonal i (P i)) :
    Function.Injective F := by
  classical
  intro P Q hPQ
  let R : (i : Fin n) → S i := P - Q
  have hFR : F R = 0 := by
    dsimp [R]
    rw [map_sub, hPQ, sub_self]
  by_contra hne
  have hRne : R ≠ 0 := by
    intro hzero
    apply hne
    exact sub_eq_zero.mp hzero
  let support : Finset (Fin n) := Finset.univ.filter fun i => R i ≠ 0
  have hsupport : support.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hRne
    funext i
    by_contra hi
    have himem : i ∈ support := by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [Pi.zero_apply] using hi
    simpa [hempty] using himem
  let i : Fin n := support.max' hsupport
  have hi : i ∈ support := Finset.max'_mem support hsupport
  have hgreater : ∀ j, i < j → R j = 0 := by
    intro j hij
    by_contra hj
    have hjmem : j ∈ support := by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [Pi.zero_apply] using hj
    have hji : j ≤ i := Finset.le_max' support j hjmem
    exact (not_le_of_gt hij) hji
  have hdiagzero : diagonal i (R i) = 0 := by
    rw [← hupper R i hgreater]
    exact congrFun hFR i
  have hRi : R i = 0 := by
    apply hdiagonal i
    simpa using hdiagzero
  exact (Finset.mem_filter.mp hi).2 hRi

private theorem range_finrank_le_codimension
    {E T : Type*} [AddCommGroup E] [Module K E] [Module.Finite K E]
    [AddCommGroup T] [Module K T]
    (V : Submodule K E) (J : E →ₗ[K] T)
    (hV : V ≤ LinearMap.ker J) :
    Module.finrank K (LinearMap.range J) ≤
      Module.finrank K E - Module.finrank K V := by
  have hker := Submodule.finrank_mono hV
  have hsum := J.finrank_range_add_finrank_ker
  omega

abbrev RFreeYDiagonalSource
    (D w L : ℕ) (points : Finset K) (h : K → ℕ) :=
  (y : Fin (L + 1)) →
    Fin (L - (y : ℕ) + 1) →
      Polynomial.degreeLT K
        (min (∑ x ∈ points, (h x - (y : ℕ))) (D - w * (y : ℕ)))

abbrev RFreeYDiagonalTarget
    (D w L : ℕ) (points : Finset K) (h : K → ℕ) :=
  (y : Fin (L + 1)) →
    Fin (L - (y : ℕ) + 1) →
      JetTarget points fun x => h x - (y : ℕ)

/-- Full `Y`-degree upper-triangular Hermite-jet codimension bound. -/
theorem rfree_yDiagonal_codimension
    {E : Type*} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (D w L : ℕ) (points : Finset K) (h : K → ℕ)
    (V : Submodule K E)
    (J : E →ₗ[K] RFreeYDiagonalTarget D w L points h)
    (embed : RFreeYDiagonalSource D w L points h →ₗ[K] E)
    (hupper : ∀ P y, (∀ j, y < j → P j = 0) →
      J (embed P) y =
        repeatedHermiteJet
          (min (∑ x ∈ points, (h x - (y : ℕ))) (D - w * (y : ℕ)))
          (L - (y : ℕ)) points (fun x => h x - (y : ℕ)) (P y))
    (hV : V ≤ LinearMap.ker J) :
    (∑ y : Fin (L + 1),
      (L - (y : ℕ) + 1) *
        min (∑ x ∈ points, (h x - (y : ℕ)))
          (D - w * (y : ℕ))) ≤
      Module.finrank K E - Module.finrank K V := by
  let diagonal : (y : Fin (L + 1)) →
      (Fin (L - (y : ℕ) + 1) →
        Polynomial.degreeLT K
          (min (∑ x ∈ points, (h x - (y : ℕ)))
            (D - w * (y : ℕ)))) →ₗ[K]
      (Fin (L - (y : ℕ) + 1) →
        JetTarget points fun x => h x - (y : ℕ)) :=
    fun y =>
      repeatedHermiteJet
        (min (∑ x ∈ points, (h x - (y : ℕ))) (D - w * (y : ℕ)))
        (L - (y : ℕ)) points (fun x => h x - (y : ℕ))
  have hdiagonal : ∀ y, Function.Injective (diagonal y) := by
    intro y
    exact repeatedHermiteJet_injective
      (min (∑ x ∈ points, (h x - (y : ℕ))) (D - w * (y : ℕ)))
      (L - (y : ℕ)) points (fun x => h x - (y : ℕ))
      (Nat.min_le_left
        (∑ x ∈ points, (h x - (y : ℕ))) (D - w * (y : ℕ)))
  have hcomp : Function.Injective (J.comp embed) := by
    apply piLinearMap_injective_of_upperTriangular
      (F := J.comp embed) (diagonal := diagonal) hdiagonal
    intro P y hy
    exact hupper P y hy
  let toRange : RFreeYDiagonalSource D w L points h →ₗ[K]
    LinearMap.range J :=
    LinearMap.codRestrict (LinearMap.range J) (J.comp embed) fun P =>
      ⟨embed P, rfl⟩
  have htoRange : Function.Injective toRange := by
    intro P Q hPQ
    apply hcomp
    exact congrArg Subtype.val hPQ
  have hrank := LinearMap.finrank_le_finrank_of_injective htoRange
  have hdomain :
      Module.finrank K (RFreeYDiagonalSource D w L points h) =
        ∑ y : Fin (L + 1),
          (L - (y : ℕ) + 1) *
            min (∑ x ∈ points, (h x - (y : ℕ)))
              (D - w * (y : ℕ)) := by
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro y _
    simp [Module.finrank_pi_fintype, finrank_degreeLT]
  rw [hdomain] at hrank
  exact hrank.trans (range_finrank_le_codimension V J hV)

def deltaShift : Poly K →ₐ[K] Poly K :=
  MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.X 1,
    MvPolynomial.X 1, MvPolynomial.X 2]

def deltaHomogenizedTranslation (x u₀ u₁ : K) :
    MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K :=
  (Polynomial.mapAlgHom (deltaShift (K := K))).comp
    (homogenizedTranslation K x u₀ u₁)

def diagonalLocalExponent (y z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 1 y + Finsupp.single 2 z

theorem deltaShift_localMonomial (f z : ℕ) :
    deltaShift (K := K) (localMonomial K f 0 z) =
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ f * MvPolynomial.X 2 ^ z := by
  rw [ContactTranslation.localMonomial_eq]
  simp [deltaShift]

theorem deltaShift_seedAffine (u₀ u₁ : K) :
    deltaShift (K := K) (seedAffine K u₀ u₁) = seedAffine K u₀ u₁ := by
  simp [deltaShift, seedAffine, ← MvPolynomial.C_mul_X_eq_monomial]

private theorem deltaShift_localMonomial_diagonal (y z : ℕ) :
    MvPolynomial.coeff (diagonalLocalExponent y z)
      (deltaShift (K := K) (localMonomial K y 0 z)) = 1 := by
  rw [deltaShift_localMonomial, MvPolynomial.X_pow_eq_monomial]
  change MvPolynomial.coeff
      (Finsupp.single 1 y + Finsupp.single 2 z)
      ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ y *
        MvPolynomial.monomial (Finsupp.single 2 z) 1) = 1
  rw [MvPolynomial.coeff_mul_monomial, add_pow]
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.sub_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [MvPolynomial.coeff_X_pow, if_pos rfl]
  · intro j hj hj0
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul]
    rw [show (↑(y.choose j) : MvPolynomial (Fin 3) K) =
        MvPolynomial.C ((y.choose j : ℕ) : K) by rfl]
    rw [mul_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial]
    split_ifs with heq
    · have hh := congrArg (fun d : Fin 3 →₀ ℕ => d 0) heq
      simp [Finsupp.add_apply] at hh
      omega
    · exact mul_zero _
  · simp

private theorem deltaShift_localMonomial_cross
    (y z z' : ℕ) (hne : z ≠ z') :
    MvPolynomial.coeff (diagonalLocalExponent y z')
      (deltaShift (K := K) (localMonomial K y 0 z)) = 0 := by
  rw [deltaShift_localMonomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial']
  split_ifs with hle
  · by_contra hc
    simp only [mul_one] at hc
    have hmem := MvPolynomial.mem_support_iff.mpr hc
    have hcoord := MvPolynomial.le_degreeOf_of_mem_support (2 : Fin 3) hmem
    have hbase : MvPolynomial.degreeOf (2 : Fin 3)
        (MvPolynomial.X 0 + MvPolynomial.X 1 : Poly K) ≤ 0 :=
      (MvPolynomial.degreeOf_add_le (2 : Fin 3) _ _).trans (by
        rw [MvPolynomial.degreeOf_X_of_ne (show (2 : Fin 3) ≠ 0 by decide),
          MvPolynomial.degreeOf_X_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
        omega)
    have hdeg := (MvPolynomial.degreeOf_pow_le (2 : Fin 3)
      (MvPolynomial.X 0 + MvPolynomial.X 1 : Poly K) y).trans
        (Nat.mul_le_mul_left y hbase)
    have hzle := hle (2 : Fin 3)
    simp [diagonalLocalExponent, Finsupp.sub_apply] at hcoord hzle
    omega
  · rfl

private theorem degreeOf_seedAffine_one (u₀ u₁ : K) :
    MvPolynomial.degreeOf (1 : Fin 3) (seedAffine K u₀ u₁) = 0 := by
  rw [seedAffine, ← MvPolynomial.C_mul_X_eq_monomial]
  apply Nat.eq_zero_of_le_zero
  apply (MvPolynomial.degreeOf_add_le (1 : Fin 3) _ _).trans
  simp only [MvPolynomial.degreeOf_C, max_le_iff, le_refl, true_and]
  exact (MvPolynomial.degreeOf_mul_le (1 : Fin 3) _ _).trans (by
    rw [MvPolynomial.degreeOf_C,
      MvPolynomial.degreeOf_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)])

private theorem degreeOf_deltaShift_seed_local_le
    (u₀ u₁ : K) (n f z : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 3)
      (deltaShift (K := K)
        (seedAffine K u₀ u₁ ^ n * localMonomial K f 0 z)) ≤ f := by
  rw [map_mul, map_pow, deltaShift_seedAffine, deltaShift_localMonomial]
  have hbase : MvPolynomial.degreeOf (1 : Fin 3)
      (MvPolynomial.X 0 + MvPolynomial.X 1 : Poly K) ≤ 1 :=
    (MvPolynomial.degreeOf_add_le (1 : Fin 3) _ _).trans (by
      rw [MvPolynomial.degreeOf_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
        MvPolynomial.degreeOf_X_self]
      omega)
  have htwo : MvPolynomial.degreeOf (1 : Fin 3)
      (MvPolynomial.X 2 : Poly K) ≤ 0 := by
    rw [MvPolynomial.degreeOf_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  calc
    MvPolynomial.degreeOf (1 : Fin 3)
        (seedAffine K u₀ u₁ ^ n *
          ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ f *
            MvPolynomial.X 2 ^ z)) ≤
      MvPolynomial.degreeOf (1 : Fin 3) (seedAffine K u₀ u₁ ^ n) +
        MvPolynomial.degreeOf (1 : Fin 3)
          ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ f *
            MvPolynomial.X 2 ^ z) := MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ n * MvPolynomial.degreeOf (1 : Fin 3) (seedAffine K u₀ u₁) +
        (f * MvPolynomial.degreeOf (1 : Fin 3)
            (MvPolynomial.X 0 + MvPolynomial.X 1 : Poly K) +
          z * MvPolynomial.degreeOf (1 : Fin 3)
            (MvPolynomial.X 2 : Poly K)) := by
      exact Nat.add_le_add (MvPolynomial.degreeOf_pow_le _ _ _)
        ((MvPolynomial.degreeOf_mul_le _ _ _).trans
          (Nat.add_le_add (MvPolynomial.degreeOf_pow_le _ _ _)
            (MvPolynomial.degreeOf_pow_le _ _ _)))
    _ ≤ f := by
      rw [degreeOf_seedAffine_one]
      simpa using Nat.add_le_add (Nat.mul_le_mul_left f hbase)
        (Nat.mul_le_mul_left z htwo)

private theorem deltaShift_seed_local_coeff_zero
    (u₀ u₁ : K) (n f y z z' : ℕ) (hf : f < y) :
    MvPolynomial.coeff (diagonalLocalExponent y z')
      (deltaShift (K := K)
        (seedAffine K u₀ u₁ ^ n * localMonomial K f 0 z)) = 0 := by
  by_contra hne
  have hmem := MvPolynomial.mem_support_iff.mpr hne
  have hle := MvPolynomial.le_degreeOf_of_mem_support (1 : Fin 3) hmem
  have hdeg := degreeOf_deltaShift_seed_local_le u₀ u₁ n f z
  have hyf : y ≤ f := by
    simpa [diagonalLocalExponent] using hle.trans hdeg
  omega

/-- The exact `Y`-degree diagonal coefficient of one `R`-free column. -/
theorem translation_rfree_column_diagonal
    (D w L : ℕ) (x u₀ u₁ a : K)
    (c : CoefficientIndex D w L 0) (k : ℕ) :
    MvPolynomial.coeff
        (diagonalLocalExponent c.1.val c.2.2.1.val)
        ((deltaHomogenizedTranslation x u₀ u₁
          (MvPolynomial.monomial (columnExponent c) a)).coeff
            (c.1.val + k)) =
      (Polynomial.taylor x
        (Polynomial.monomial c.2.2.2.val a)).coeff k := by
  have hcR : c.2.1.val = 0 := by
    have := c.2.1.isLt
    omega
  rw [deltaHomogenizedTranslation, AlgHom.comp_apply,
    Polynomial.coeff_mapAlgHom_apply]
  rw [translation_column_coeff]
  simp only [map_smul, MvPolynomial.coeff_smul,
    RingHom.id_apply, smul_eq_mul]
  unfold blockEntry
  rw [map_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single ⟨c.1.val, by omega⟩]
  · simp only [Fin.val_mk, hcR, Nat.le_add_right, if_true,
      Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one,
      map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [deltaShift_localMonomial_diagonal]
    simp [Polynomial.taylor_monomial, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow]
    ring_nf
    simp
  · intro f _ hne
    have hf : f.val < c.1.val := by
      have hle : f.val ≤ c.1.val := by omega
      have hneval : f.val ≠ c.1.val := by
        intro heq
        exact hne (Fin.ext heq)
      omega
    split_ifs with hfr
    · simp only [map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
      simp only [Fin.val_eq_zero]
      rw [deltaShift_seed_local_coeff_zero u₀ u₁
        (c.1.val - f.val) f.val c.1.val c.2.2.1.val c.2.2.1.val hf,
        mul_zero]
    · simp
  · simp

theorem translation_rfree_column_below_diagonal
    (D w L : ℕ) (x u₀ u₁ a : K)
    (c : CoefficientIndex D w L 0) (y z k : ℕ)
    (hy : c.1.val < y) :
    MvPolynomial.coeff (diagonalLocalExponent y z)
        ((deltaHomogenizedTranslation x u₀ u₁
          (MvPolynomial.monomial (columnExponent c) a)).coeff (y + k)) = 0 := by
  rw [deltaHomogenizedTranslation, AlgHom.comp_apply,
    Polynomial.coeff_mapAlgHom_apply, translation_column_coeff]
  simp only [map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  unfold blockEntry
  rw [map_sum, MvPolynomial.coeff_sum]
  apply mul_eq_zero_of_right a
  apply Finset.sum_eq_zero
  intro f _
  split_ifs with hfr
  · simp only [map_smul, MvPolynomial.coeff_smul, smul_eq_mul,
      Fin.val_eq_zero]
    have hf : f.val < y := by
      have := f.isLt
      omega
    rw [deltaShift_seed_local_coeff_zero u₀ u₁
      (c.1.val - f.val) f.val y c.2.2.1.val z hf, mul_zero]
  · simp

theorem translation_rfree_column_cross_channel
    (D w L : ℕ) (x u₀ u₁ a : K)
    (c : CoefficientIndex D w L 0) (z k : ℕ)
    (hz : c.2.2.1.val ≠ z) :
    MvPolynomial.coeff (diagonalLocalExponent c.1.val z)
        ((deltaHomogenizedTranslation x u₀ u₁
          (MvPolynomial.monomial (columnExponent c) a)).coeff
            (c.1.val + k)) = 0 := by
  rw [deltaHomogenizedTranslation, AlgHom.comp_apply,
    Polynomial.coeff_mapAlgHom_apply, translation_column_coeff]
  simp only [map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  unfold blockEntry
  rw [map_sum, MvPolynomial.coeff_sum]
  apply mul_eq_zero_of_right a
  rw [Finset.sum_eq_single ⟨c.1.val, by omega⟩]
  · simp only [Fin.val_eq_zero, Nat.le_add_right, if_true,
      Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one,
      map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [deltaShift_localMonomial_cross (K := K) c.1.val c.2.2.1.val z hz,
      mul_zero]
  · intro f _ hne
    have hf : f.val < c.1.val := by
      have hle : f.val ≤ c.1.val := by omega
      have hneval : f.val ≠ c.1.val := by
        intro heq
        exact hne (Fin.ext heq)
      omega
    split_ifs with hfr
    · simp only [map_smul, MvPolynomial.coeff_smul, smul_eq_mul,
        Fin.val_eq_zero]
      rw [deltaShift_seed_local_coeff_zero u₀ u₁
        (c.1.val - f.val) f.val c.1.val c.2.2.1.val z hf, mul_zero]
    · simp
  · simp

def rfreeColumnIndex (D w L q : ℕ) (y : Fin (L + 1))
    (z : Fin (L - y.val + 1)) (hq : q ≤ D - w * y.val) (e : Fin q) :
    CoefficientIndex D w L 0 :=
  ⟨y, ⟨⟨0, by omega⟩,
    ⟨⟨z.val, by have := z.isLt; omega⟩,
      ⟨e.val, by
        simp only [Fin.val_mk, Nat.mul_zero, Nat.sub_zero]
        exact e.isLt.trans_le hq⟩⟩⟩⟩

def rfreeEmbedPolynomial (D w L : ℕ) (points : Finset K) (h : K → ℕ)
    (P : RFreeYDiagonalSource D w L points h) : MvPolynomial (Fin 4) K :=
  ∑ y : Fin (L + 1), ∑ z : Fin (L - y.val + 1),
    ∑ e : Fin (min (∑ x ∈ points, (h x - y.val)) (D - w * y.val)),
      MvPolynomial.monomial
        (columnExponent (rfreeColumnIndex D w L _ y z (Nat.min_le_right _ _) e))
        ((P y z : Polynomial K).coeff e.val)

theorem rfreeEmbedPolynomial_mem (D w L : ℕ)
    (points : Finset K) (h : K → ℕ)
    (P : RFreeYDiagonalSource D w L points h) :
    rfreeEmbedPolynomial D w L points h P ∈ globalCoefficientBox K D w L 0 := by
  classical
  unfold rfreeEmbedPolynomial
  apply Submodule.sum_mem
  intro y _
  apply Submodule.sum_mem
  intro z _
  apply Submodule.sum_mem
  intro e _
  exact columnMonomial_mem K D w L 0
    (rfreeColumnIndex D w L _ y z (Nat.min_le_right _ _) e) _

def rfreeEmbed (D w L : ℕ) (points : Finset K) (h : K → ℕ) :
    RFreeYDiagonalSource D w L points h →ₗ[K]
      globalCoefficientBox K D w L 0 where
  toFun P := ⟨rfreeEmbedPolynomial D w L points h P,
    rfreeEmbedPolynomial_mem D w L points h P⟩
  map_add' P Q := by
    apply Subtype.ext
    simp [rfreeEmbedPolynomial, MvPolynomial.coeff_add,
      Finset.sum_add_distrib]
  map_smul' a P := by
    apply Subtype.ext
    simp [rfreeEmbedPolynomial, MvPolynomial.coeff_smul,
      Finset.smul_sum, MvPolynomial.smul_monomial, smul_eq_mul]

def rfreeSelectedJetMap (D w L : ℕ) (points : Finset K) (h : K → ℕ)
    (u₀ u₁ : K → K) :
    globalCoefficientBox K D w L 0 →ₗ[K]
      RFreeYDiagonalTarget D w L points h where
  toFun Q y z x k :=
    MvPolynomial.coeff (diagonalLocalExponent y.val z.val)
      ((deltaHomogenizedTranslation (x : K) (u₀ x) (u₁ x) Q.1).coeff
        (y.val + k.val))
  map_add' P Q := by
    funext y z x k
    simp [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add]
  map_smul' a P := by
    funext y z x k
    simp [map_smul, Polynomial.coeff_smul, MvPolynomial.coeff_smul,
      smul_eq_mul]

theorem rfreeSelectedJetMap_embed_upper
    (D w L : ℕ) (points : Finset K) (h : K → ℕ)
    (u₀ u₁ : K → K)
    (P : RFreeYDiagonalSource D w L points h)
    (y : Fin (L + 1)) (hy : ∀ j, y < j → P j = 0) :
    rfreeSelectedJetMap D w L points h u₀ u₁
        (rfreeEmbed D w L points h P) y =
      repeatedHermiteJet
        (min (∑ x ∈ points, (h x - y.val)) (D - w * y.val))
        (L - y.val) points (fun x => h x - y.val) (P y) := by
  classical
  funext z x k
  change MvPolynomial.coeff (diagonalLocalExponent y.val z.val)
      ((deltaHomogenizedTranslation (x : K) (u₀ x) (u₁ x)
        (rfreeEmbedPolynomial D w L points h P)).coeff
          (y.val + k.val)) =
    (Polynomial.taylor (x : K) (P y z : Polynomial K)).coeff k.val
  unfold rfreeEmbedPolynomial
  simp only [map_sum]
  change (MvPolynomial.lcoeff K (diagonalLocalExponent y.val z.val))
      ((Polynomial.lcoeff (Poly K) (y.val + k.val))
        (∑ x_1, ∑ x_2, ∑ x_3,
          (deltaHomogenizedTranslation (x : K) (u₀ x) (u₁ x))
            (MvPolynomial.monomial
              (columnExponent
                (rfreeColumnIndex D w L
                  (min (∑ a ∈ points, (h a - x_1.val))
                    (D - w * x_1.val))
                  x_1 x_2 (Nat.min_le_right _ _) x_3))
              ((P x_1 x_2 : Polynomial K).coeff x_3.val)))) = _
  simp only [map_sum]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single z]
    · let q := min (∑ a ∈ points, (h a - y.val)) (D - w * y.val)
      have hterm (e : Fin q) :
          (MvPolynomial.lcoeff K (diagonalLocalExponent y.val z.val))
              ((Polynomial.lcoeff (Poly K) (y.val + k.val))
                ((deltaHomogenizedTranslation (x : K) (u₀ x) (u₁ x))
                  (MvPolynomial.monomial
                    (columnExponent
                      (rfreeColumnIndex D w L q y z
                        (Nat.min_le_right _ _) e))
                    ((P y z : Polynomial K).coeff e.val)))) =
            (Polynomial.taylor (x : K)
              (Polynomial.monomial e.val
                ((P y z : Polynomial K).coeff e.val))).coeff k.val := by
        simpa [LinearMap.coe_mk, AddHom.coe_mk, rfreeColumnIndex] using
          translation_rfree_column_diagonal D w L
            (x : K) (u₀ x) (u₁ x)
            ((P y z : Polynomial K).coeff e.val)
            (rfreeColumnIndex D w L q y z (Nat.min_le_right _ _) e)
            k.val
      change (∑ e : Fin q,
          (MvPolynomial.lcoeff K (diagonalLocalExponent y.val z.val))
            ((Polynomial.lcoeff (Poly K) (y.val + k.val))
              ((deltaHomogenizedTranslation (x : K) (u₀ x) (u₁ x))
                (MvPolynomial.monomial
                  (columnExponent
                    (rfreeColumnIndex D w L q y z
                      (Nat.min_le_right _ _) e))
                  ((P y z : Polynomial K).coeff e.val))))) = _
      simp_rw [hterm]
      have hpoly :
          (∑ e : Fin q, Polynomial.monomial e.val
            ((P y z : Polynomial K).coeff e.val)) =
            (P y z : Polynomial K) := by
        calc
          (∑ e : Fin q, Polynomial.monomial e.val
              ((P y z : Polynomial K).coeff e.val)) =
              (P y z : Polynomial K).sum
                (fun n a => Polynomial.monomial n a) :=
            Polynomial.sum_fin (p := (P y z : Polynomial K))
              (n := q) (fun n a => Polynomial.monomial n a)
              (fun _ => Polynomial.monomial_zero_right _)
              (by simpa [q] using Polynomial.mem_degreeLT.mp (P y z).property)
          _ = (P y z : Polynomial K) :=
            (P y z : Polynomial K).sum_monomial_eq
      change ∑ e : Fin q,
          (Polynomial.lcoeff K k.val)
            (Polynomial.taylor (x : K)
              (Polynomial.monomial e.val
                ((P y z : Polynomial K).coeff e.val))) = _
      rw [← map_sum (Polynomial.lcoeff K k.val),
        ← map_sum (Polynomial.taylor (x : K)), hpoly]
      rfl
    · intro z' _ hz_ne
      apply Finset.sum_eq_zero
      intro e _
      simpa [LinearMap.coe_mk, AddHom.coe_mk, rfreeColumnIndex] using
        translation_rfree_column_cross_channel D w L
          (x : K) (u₀ x) (u₁ x)
          ((P y z' : Polynomial K).coeff e.val)
          (rfreeColumnIndex D w L _ y z' (Nat.min_le_right _ _) e)
          z.val k.val (by
            simp only [rfreeColumnIndex]
            intro hzval
            exact hz_ne (Fin.ext hzval))
    · simp
  · intro i _ hiy_ne
    by_cases hiy : i < y
    · apply Finset.sum_eq_zero
      intro z' _
      apply Finset.sum_eq_zero
      intro e _
      simpa [LinearMap.coe_mk, AddHom.coe_mk, rfreeColumnIndex] using
        translation_rfree_column_below_diagonal D w L
          (x : K) (u₀ x) (u₁ x)
          ((P i z' : Polynomial K).coeff e.val)
          (rfreeColumnIndex D w L _ i z' (Nat.min_le_right _ _) e)
          y.val z.val k.val (by exact_mod_cast hiy)
    · have hyi : y < i := by
        have hle : y ≤ i := le_of_not_gt hiy
        exact lt_of_le_of_ne hle (Ne.symm hiy_ne)
      have hP := hy i hyi
      simp [hP]
  · simp

/-- The concrete `R`-free coefficient-box codimension bound.  A caller only
has to place its constrained subspace in the kernel of the selected jet map. -/
theorem rfree_globalCoefficientBox_codimension
    (D w L : ℕ) (points : Finset K) (h : K → ℕ)
    (u₀ u₁ : K → K)
    [Module.Finite K (globalCoefficientBox K D w L 0)]
    (V : Submodule K (globalCoefficientBox K D w L 0))
    (hV : V ≤ LinearMap.ker
      (rfreeSelectedJetMap D w L points h u₀ u₁)) :
    (∑ y : Fin (L + 1),
      (L - y.val + 1) *
        min (∑ x ∈ points, (h x - y.val))
          (D - w * y.val)) ≤
      Module.finrank K (globalCoefficientBox K D w L 0) -
        Module.finrank K V := by
  exact rfree_yDiagonal_codimension D w L points h V
    (rfreeSelectedJetMap D w L points h u₀ u₁)
    (rfreeEmbed D w L points h)
    (rfreeSelectedJetMap_embed_upper D w L points h u₀ u₁) hV

theorem profileA_five_channel_diagonal_sum_of_le
    (D : ℕ) (hD : D ≤ 567522) (points : Finset K) (h : K → ℕ) :
    (∑ y : Fin 84440,
      (84439 - y.val + 1) *
        min (∑ x ∈ points, (h x - y.val))
          (D - 131071 * y.val)) =
      84440 * min (∑ x ∈ points, h x) D +
      84439 * min (∑ x ∈ points, (h x - 1)) (D - 131071) +
      84438 * min (∑ x ∈ points, (h x - 2)) (D - 2 * 131071) +
      84437 * min (∑ x ∈ points, (h x - 3)) (D - 3 * 131071) +
      84436 * min (∑ x ∈ points, (h x - 4)) (D - 4 * 131071) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.mul_zero]
  have hzero (i : Fin 84435) :
      D - 131071 * (i.val + 1 + 1 + 1 + 1 + 1) = 0 := by omega
  simp_rw [hzero]
  norm_num
  omega

theorem rfree_profileA_five_channel_codimension_of_le
    (D : ℕ) (hD : D ≤ 567522)
    (points : Finset K) (h : K → ℕ) (u₀ u₁ : K → K)
    [Module.Finite K (globalCoefficientBox K D 131071 84439 0)]
    (V : Submodule K (globalCoefficientBox K D 131071 84439 0))
    (hV : V ≤ LinearMap.ker
      (rfreeSelectedJetMap D 131071 84439 points h u₀ u₁)) :
    84440 * min (∑ x ∈ points, h x) D +
      84439 * min (∑ x ∈ points, (h x - 1)) (D - 131071) +
      84438 * min (∑ x ∈ points, (h x - 2)) (D - 2 * 131071) +
      84437 * min (∑ x ∈ points, (h x - 3)) (D - 3 * 131071) +
      84436 * min (∑ x ∈ points, (h x - 4)) (D - 4 * 131071) ≤
        Module.finrank K (globalCoefficientBox K D 131071 84439 0) -
          Module.finrank K V := by
  have hbound := rfree_globalCoefficientBox_codimension
    D 131071 84439 points h u₀ u₁ V hV
  rw [profileA_five_channel_diagonal_sum_of_le D hD] at hbound
  exact hbound

private theorem profileA_coefficientCount_five_terms
    (D : ℕ) (hD : D ≤ 567522) :
    coefficientCount D 131071 84439 0 =
      84440 * D +
      84439 * (D - 131071) +
      84438 * (D - 2 * 131071) +
      84437 * (D - 3 * 131071) +
      84436 * (D - 4 * 131071) := by
  have hsplit : 84439 + 1 = 5 + (84439 + 1 - 5) := by omega
  unfold coefficientCount
  rw [hsplit, Finset.sum_range_add]
  have htail :
      (∑ i ∈ Finset.range (84439 + 1 - 5),
        ∑ j ∈ Finset.range (0 + 1),
          (5 + (84439 + 1 - 5) - (5 + i)) *
            (D - 131071 * (5 + i) - (131071 - 1) * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hzero : D - 131071 * (5 + i) = 0 := by omega
    simp [hzero]
  rw [htail, add_zero]
  norm_num [Finset.sum_range_succ]

set_option maxRecDepth 100000 in
theorem profileA_five_channel_capacity
    (D : ℕ) (hD : D ≤ 567522) (points : Finset K) (h : K → ℕ)
    (hcard : points.card = 182032)
    (hgap : D - (∑ x ∈ points, h x) ≤ 50962) :
    coefficientCount D 131071 84439 0 -
        (84440 * min (∑ x ∈ points, h x) D +
        84439 * min (∑ x ∈ points, (h x - 1)) (D - 131071) +
        84438 * min (∑ x ∈ points, (h x - 2)) (D - 2 * 131071) +
        84437 * min (∑ x ∈ points, (h x - 3)) (D - 3 * 131071) +
        84436 * min (∑ x ∈ points, (h x - 4)) (D - 4 * 131071)) ≤
      44188803040 := by
  let H := ∑ x ∈ points, h x
  let S : ℕ → ℕ := fun y => ∑ x ∈ points, (h x - y)
  change D - H ≤ 50962 at hgap
  change coefficientCount D 131071 84439 0 -
      (84440 * min (S 0) D +
      84439 * min (S 1) (D - 131071) +
      84438 * min (S 2) (D - 2 * 131071) +
      84437 * min (S 3) (D - 3 * 131071) +
      84436 * min (S 4) (D - 4 * 131071)) ≤ 44188803040
  have hshift (y : ℕ) : H ≤ S y + y * points.card := by
    dsimp only [H, S]
    calc
      (∑ x ∈ points, h x) ≤
          ∑ x ∈ points, ((h x - y) + y) := by
        apply Finset.sum_le_sum
        intro x _
        omega
      _ = (∑ x ∈ points, (h x - y)) + y * points.card := by
        simp [Finset.sum_add_distrib, mul_comm]
  have hs0 := hshift 0
  have hs1 := hshift 1
  have hs2 := hshift 2
  rw [hcard] at hs0 hs1 hs2
  have hr0 : D - min (S 0) D ≤ 50962 := by omega
  have hr1 : (D - 131071) - min (S 1) (D - 131071) ≤ 101923 := by
    omega
  have hr2 : (D - 2 * 131071) - min (S 2) (D - 2 * 131071) ≤
      152884 := by
    have hS2 : H ≤ S 2 + 364064 := by omega
    let A := D - 2 * 131071
    let B := S 2
    have hAB : A ≤ B + 152884 := by
      dsimp only [A, B]
      omega
    change A - min B A ≤ 152884
    rcases le_total A B with hle | hle
    · rw [Nat.min_eq_right hle, Nat.sub_self]
      exact Nat.zero_le _
    · rw [Nat.min_eq_left hle]
      exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using hAB)
  have hr3 : (D - 3 * 131071) - min (S 3) (D - 3 * 131071) ≤
      174309 :=
    (Nat.sub_le _ _).trans (by omega)
  have hr4 : (D - 4 * 131071) - min (S 4) (D - 4 * 131071) ≤
      43238 :=
    (Nat.sub_le _ _).trans (by omega)
  rw [profileA_coefficientCount_five_terms D hD]
  omega

end
end ProximityPrize.SubmissionLower.RFreeJetCodimension
