/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# Sequential specialization and factor selection

This file isolates the second factor-selection step.  Starting with
`R ∈ F[Z][X][Y]`, it first chooses `x₀` away from the leading-coefficient and
fixed-degree-resultant exceptional sets.  It then selects one positive-`Y`
normalized factor `H ∈ F[Z][Y]` shared by many specialized roots.

The output required by Taylor extraction is deliberately representation-free:
`H` divides `R(x₀,Y,Z)`, and its image in `Frac(F[Z])[Y]` is coprime to its
formal derivative.
-/

namespace ProximityPrize.SubmissionLower.SequentialFactorSelection

open Polynomial

noncomputable section

variable {F : Type} [Field F] [DecidableEq F]

noncomputable local instance polynomialNormalizationMonoid
    {R : Type} [CommRing R] [IsDomain R] [NormalizationMonoid R] :
    NormalizationMonoid R[X] where
  normUnit polynomial :=
    ⟨Polynomial.C ↑(normUnit polynomial.leadingCoeff),
      Polynomial.C ↑(normUnit polynomial.leadingCoeff)⁻¹,
      by rw [← Polynomial.C_mul, Units.mul_inv, Polynomial.C_1],
      by rw [← Polynomial.C_mul, Units.inv_mul, Polynomial.C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_one := Units.ext (by simp)
  normUnit_mul_units unit hunit := Units.ext <| by
    dsimp only [Units.val_mul]
    obtain ⟨_, ⟨witness, rfl⟩, hwitness⟩ := isUnit_iff.mp ⟨unit, rfl⟩
    rw [Polynomial.leadingCoeff_mul, ← hwitness,
      Polynomial.leadingCoeff_C,
      normUnit_mul_units _ (Polynomial.leadingCoeff_ne_zero.mpr hunit),
      Units.eq_inv_mul_iff_mul_eq, Units.val_mul, Polynomial.C_mul,
      ← mul_assoc, ← hwitness, ← Polynomial.C_mul]
    simp

/-- Polynomials in `F[Z][X][Y]`, with `Y` outermost. -/
abbrev TriPolynomial (F : Type) [Semiring F] :=
  Polynomial (Polynomial (Polynomial F))

/-- Polynomials in `F[Z][Y]`, with `Y` outermost. -/
abbrev BiPolynomial (F : Type) [Semiring F] := Polynomial (Polynomial F)

/-- Evaluate the `X` variable while retaining `Z` and `Y`. -/
def specializeX (x : F) : TriPolynomial F →+* BiPolynomial F :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (Polynomial.C x))

/-- The fixed-degree resultant used before specialization.  Fixing the size makes
the construction commute with specialization even at exceptional points. -/
def derivativeResultant (R : TriPolynomial F) : Polynomial (Polynomial F) :=
  Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)

open Classical in
/-- A polynomial over `F[Z]` has at most its degree many distinct roots of the
form `C x`, for injectively chosen field elements `x`. -/
theorem card_eval_C_eq_zero_le_natDegree
    (P : Polynomial (Polynomial F)) (hP : P ≠ 0)
    {Seed : Type} [DecidableEq Seed] (seeds : Finset Seed) (x : Seed → F)
    (hx : Set.InjOn x (seeds : Set Seed)) :
    (seeds.filter fun seed => P.eval (Polynomial.C (x seed)) = 0).card ≤
      P.natDegree := by
  classical
  let roots := seeds.filter fun seed => P.eval (Polynomial.C (x seed)) = 0
  have hsubset : (roots : Set Seed) ⊆ (seeds : Set Seed) := by
    intro seed hseed
    exact (Finset.mem_filter.mp hseed).1
  have hinjX : Set.InjOn (fun seed => Polynomial.C (x seed)) (roots : Set Seed) := by
    intro a ha b hb hab
    apply hx (hsubset ha) (hsubset hb)
    exact Polynomial.C_injective hab
  have hcard : (roots.image fun seed => Polynomial.C (x seed)).card = roots.card :=
    Finset.card_image_iff.mpr hinjX
  have hroots :
      (roots.image fun seed => Polynomial.C (x seed)).val ⊆ P.roots := by
    intro root hroot
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp
      (show root ∈ roots.image (fun seed => Polynomial.C (x seed)) from hroot)
    exact (Polynomial.mem_roots hP).mpr (Finset.mem_filter.mp hseed).2
  calc
    roots.card = (roots.image fun seed => Polynomial.C (x seed)).card := hcard.symm
    _ ≤ P.natDegree := Polynomial.card_le_degree_of_subset_roots hroots

open Classical in
/-- Avoid two nonzero polynomial exceptional sets simultaneously. -/
theorem exists_avoiding_two_eval_C
    (A B : Polynomial (Polynomial F)) (hA : A ≠ 0) (hB : B ≠ 0)
    (candidates : Finset F)
    (hcard : A.natDegree + B.natDegree < candidates.card) :
    ∃ x ∈ candidates,
      A.eval (Polynomial.C x) ≠ 0 ∧ B.eval (Polynomial.C x) ≠ 0 := by
  classical
  let badA := candidates.filter fun x => A.eval (Polynomial.C x) = 0
  let badB := candidates.filter fun x => B.eval (Polynomial.C x) = 0
  have hbadA : badA.card ≤ A.natDegree := by
    simpa [badA] using
      card_eval_C_eq_zero_le_natDegree A hA candidates id
        (Set.injOn_id (s := (candidates : Set F)))
  have hbadB : badB.card ≤ B.natDegree := by
    simpa [badB] using
      card_eval_C_eq_zero_le_natDegree B hB candidates id
        (Set.injOn_id (s := (candidates : Set F)))
  by_contra hnone
  push Not at hnone
  have hcover : candidates ⊆ badA ∪ badB := by
    intro x hx
    by_cases hAx : A.eval (Polynomial.C x) = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hAx⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx, hnone x hx hAx⟩)
  have := (Finset.card_le_card hcover).trans
    (Finset.card_union_le badA badB)
  omega

open Classical in
/-- The leading coefficient and derivative resultant are the only two
exceptional polynomials needed to choose `x₀`. -/
theorem exists_good_specialization
    (R : TriPolynomial F) (hR : R ≠ 0)
    (hresultant : derivativeResultant R ≠ 0)
    (candidates : Finset F)
    (hcard : R.leadingCoeff.natDegree + (derivativeResultant R).natDegree <
      candidates.card) :
    ∃ x₀ ∈ candidates,
      (specializeX x₀ R).natDegree = R.natDegree ∧
      (derivativeResultant R).eval (Polynomial.C x₀) ≠ 0 := by
  obtain ⟨x₀, hx₀, hlead, hres⟩ := exists_avoiding_two_eval_C
    R.leadingCoeff (derivativeResultant R)
    (Polynomial.leadingCoeff_ne_zero.mpr hR) hresultant candidates hcard
  refine ⟨x₀, hx₀, ?_, hres⟩
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero Polynomial.natDegree_map_le
  simpa [specializeX] using hlead

/-- Embed `F[Z][Y]` into `Frac(F[Z])[Y]`. -/
def fractionMap (P : BiPolynomial F) :
    Polynomial (FractionRing (Polynomial F)) :=
  P.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))

/-- A nonvanishing fixed-degree derivative resultant after `X := x₀`
makes the specialized polynomial separable over `Frac(F[Z])`. -/
theorem fractionMap_specializeX_separable
    (R : TriPolynomial F) (x₀ : F) (hpositive : 0 < R.natDegree)
    (hresultant :
      (derivativeResultant R).eval (Polynomial.C x₀) ≠ 0) :
    (fractionMap (specializeX x₀ R)).Separable := by
  let A : Polynomial F :=
    (derivativeResultant R).eval (Polynomial.C x₀)
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  let S : BiPolynomial F := specializeX x₀ R
  let f : Polynomial K := fractionMap S
  let g : Polynomial K := f.derivative
  have hA : A ≠ 0 := by simpa [A] using hresultant
  have hφinj : Function.Injective φ := IsFractionRing.injective (Polynomial F) K
  have hφA : φ A ≠ 0 := fun h => hA (hφinj (h.trans (map_zero φ).symm))
  have hfDegree : f.natDegree ≤ R.natDegree := by
    exact Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
  have hgDegree : g.natDegree ≤ R.natDegree - 1 := by
    exact (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hfDegree 1)
  have hres : Polynomial.resultant f g R.natDegree (R.natDegree - 1) = φ A := by
    change Polynomial.resultant
      (Polynomial.map φ (specializeX x₀ R))
      (Polynomial.derivative (Polynomial.map φ (specializeX x₀ R)))
      R.natDegree (R.natDegree - 1) = φ A
    rw [Polynomial.derivative_map]
    rw [Polynomial.resultant_map_map]
    rw [show Polynomial.derivative (specializeX x₀ R) =
        Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) R.derivative by
      simpa [specializeX] using
        (Polynomial.derivative_map R
          (Polynomial.evalRingHom (Polynomial.C x₀)))]
    change φ (Polynomial.resultant
      (Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) R)
      (Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) R.derivative)
      R.natDegree (R.natDegree - 1)) = φ A
    rw [Polynomial.resultant_map_map]
    rfl
  obtain ⟨p, q, _hp, _hq, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hfDegree hgDegree
      (Or.inl hpositive.ne')
  rw [hres] at hbezout
  refine ⟨Polynomial.C (φ A)⁻¹ * p, Polynomial.C (φ A)⁻¹ * q, ?_⟩
  calc
    (Polynomial.C (φ A)⁻¹ * p) * f +
        (Polynomial.C (φ A)⁻¹ * q) * g =
      Polynomial.C (φ A)⁻¹ * (f * p + g * q) := by ring
    _ = Polynomial.C (φ A)⁻¹ * Polynomial.C (φ A) := by rw [hbezout]
    _ = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hφA, Polynomial.C_1]

open Classical in
/-- Combined good-specialization contract: degree is preserved and the result is
separable over the coefficient fraction field. -/
theorem exists_good_separable_specialization
    (R : TriPolynomial F) (hR : R ≠ 0) (hpositive : 0 < R.natDegree)
    (hresultant : derivativeResultant R ≠ 0)
    (candidates : Finset F)
    (hcard : R.leadingCoeff.natDegree + (derivativeResultant R).natDegree <
      candidates.card) :
    ∃ x₀ ∈ candidates,
      (specializeX x₀ R).natDegree = R.natDegree ∧
      (derivativeResultant R).eval (Polynomial.C x₀) ≠ 0 ∧
      (fractionMap (specializeX x₀ R)).Separable := by
  obtain ⟨x₀, hx₀, hdegree, hres⟩ :=
    exists_good_specialization R hR hresultant candidates hcard
  exact ⟨x₀, hx₀, hdegree, hres,
    fractionMap_specializeX_separable R x₀ hpositive hres⟩

/-- Evaluate `F[Z][Y]` at `(Z,Y)=(z,y)`. -/
def evalZY (z y : F) (P : BiPolynomial F) : F :=
  (P.map (Polynomial.evalRingHom z)).eval y

/-- Distinct positive-`Y` normalized factors of a bivariate polynomial. -/
def positiveYFactors (P : BiPolynomial F) : Finset (BiPolynomial F) :=
  (UniqueFactorizationMonoid.normalizedFactors P).toFinset.filter
    (fun H => 0 < H.natDegree)

/-- A seed is exceptional because a normalized factor constant in `Y` vanishes at `z`. -/
def IsContentRoot (P : BiPolynomial F) (z : F) : Prop :=
  ∃ H ∈ UniqueFactorizationMonoid.normalizedFactors P,
    H.natDegree = 0 ∧ (H.coeff 0).eval z = 0

lemma mem_positiveYFactors_iff {P H : BiPolynomial F} :
    H ∈ positiveYFactors P ↔
      H ∈ UniqueFactorizationMonoid.normalizedFactors P ∧ 0 < H.natDegree := by
  classical
  simp [positiveYFactors]

/-- The second factor count is bounded by the same outer `Y`-degree. -/
theorem card_positiveYFactors_le_natDegree (P : BiPolynomial F) (hP : P ≠ 0) :
    (positiveYFactors P).card ≤ P.natDegree := by
  classical
  let factors := UniqueFactorizationMonoid.normalizedFactors P
  let positive := factors.toFinset.filter (fun H => 0 < H.natDegree)
  have hpositive : positive = positiveYFactors P := by
    simp [positive, positiveYFactors, factors]
  have hcard : positive.card ≤ ∑ H ∈ positive, H.natDegree := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun H hH => (Finset.mem_filter.mp hH).2
  have hsubset : positive ⊆ factors.toFinset := fun _ h => (Finset.mem_filter.mp h).1
  have hsumSubset :
      (∑ H ∈ positive, H.natDegree) ≤ ∑ H ∈ factors.toFinset, H.natDegree :=
    Finset.sum_le_sum_of_subset hsubset
  have hsumCount :
      (∑ H ∈ factors.toFinset, H.natDegree) ≤
        ∑ H ∈ factors.toFinset, factors.count H * H.natDegree := by
    refine Finset.sum_le_sum ?_
    intro H hH
    exact Nat.le_mul_of_pos_left H.natDegree
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hH))
  have hcounted :
      (∑ H ∈ factors.toFinset, factors.count H * H.natDegree) =
        (factors.map Polynomial.natDegree).sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count
        (s := factors) (f := fun H => H.natDegree)).symm
  have hzero : (0 : BiPolynomial F) ∉ factors := by
    simpa [factors] using
      (UniqueFactorizationMonoid.zero_notMem_normalizedFactors P)
  have hprodDegree :
      (factors.map Polynomial.natDegree).sum = factors.prod.natDegree :=
    (Polynomial.natDegree_multiset_prod factors hzero).symm
  have hassociated : Associated factors.prod P := by
    simpa [factors] using
      (UniqueFactorizationMonoid.prod_normalizedFactors (a := P) hP)
  have hdegree : factors.prod.natDegree = P.natDegree := by
    apply Polynomial.natDegree_eq_of_degree_eq
    exact Polynomial.degree_eq_degree_of_associated hassociated
  rw [← hpositive]
  exact hcard.trans
    (hsumSubset.trans (hsumCount.trans_eq (hcounted.trans (hprodDegree.trans hdegree))))

/-- Away from content roots, every specialized root is killed by a positive-`Y` factor. -/
theorem exists_positiveYFactor_of_evalZY_eq_zero
    (P : BiPolynomial F) (hP : P ≠ 0) (z y : F)
    (hroot : evalZY z y P = 0) (hcontent : ¬ IsContentRoot P z) :
    ∃ H ∈ positiveYFactors P, evalZY z y H = 0 := by
  classical
  let factors := UniqueFactorizationMonoid.normalizedFactors P
  let φ : BiPolynomial F →+* F :=
    (Polynomial.evalRingHom y).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  have hassociated : Associated factors.prod P := by
    simpa [factors] using
      (UniqueFactorizationMonoid.prod_normalizedFactors (a := P) hP)
  have hmapped : Associated (φ factors.prod) (φ P) :=
    Associated.map (φ : BiPolynomial F →* F) hassociated
  have hprod : φ factors.prod = 0 :=
    hmapped.eq_zero_iff.mpr (by simpa [φ, evalZY] using hroot)
  have hmapProd : (factors.map φ).prod = 0 := by
    simpa [map_multiset_prod] using hprod
  obtain ⟨H, hH, hHzero⟩ := Multiset.mem_map.mp
    (Multiset.prod_eq_zero_iff.mp hmapProd)
  have hnormalized : H ∈ UniqueFactorizationMonoid.normalizedFactors P := by
    simpa [factors] using hH
  have hHeval : evalZY z y H = 0 := by simpa [φ, evalZY] using hHzero
  have hpositive : 0 < H.natDegree := by
    by_contra hnot
    have hdegree : H.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    apply hcontent
    refine ⟨H, hnormalized, hdegree, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree] at hHeval
    simpa [evalZY] using hHeval
  exact ⟨H, mem_positiveYFactors_iff.mpr ⟨hnormalized, hpositive⟩, hHeval⟩

/-- A content root kills every coefficient of the whole bivariate polynomial. -/
theorem coeff_eval_eq_zero_of_contentRoot
    (P : BiPolynomial F) (z : F) (hcontent : IsContentRoot P z) (i : ℕ) :
    (P.coeff i).eval z = 0 := by
  classical
  obtain ⟨H, hH, hdegree, hHzero⟩ := hcontent
  obtain ⟨K, rfl⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hH
  have hmapH : H.map (Polynomial.evalRingHom z) = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree]
    simpa using hHzero
  have hmapProduct : (H * K).map (Polynomial.evalRingHom z) = 0 := by
    simp [Polynomial.map_mul, hmapH]
  calc
    ((H * K).coeff i).eval z =
        ((H * K).map (Polynomial.evalRingHom z)).coeff i := by
      rw [Polynomial.coeff_map]
      rw [Polynomial.coe_evalRingHom]
    _ = 0 := by rw [hmapProduct, Polynomial.coeff_zero]

open Classical in
/-- Any nonzero coefficient witness of degree at most `72` bounds the second content loss. -/
theorem card_contentRoots_le_seventyTwo
    {Seed : Type} [DecidableEq Seed]
    (P : BiPolynomial F) (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed)) (i : ℕ)
    (hcoeff : P.coeff i ≠ 0) (hdegree : (P.coeff i).natDegree ≤ 72) :
    (seeds.filter fun seed => IsContentRoot P (z seed)).card ≤ 72 := by
  classical
  let bad := seeds.filter fun seed => IsContentRoot P (z seed)
  have hsubset : (bad : Set Seed) ⊆ (seeds : Set Seed) := by
    intro seed hseed
    exact (Finset.mem_filter.mp hseed).1
  have hinj : Set.InjOn z (bad : Set Seed) := hz.mono hsubset
  have hcard : (bad.image z).card = bad.card := Finset.card_image_iff.mpr hinj
  have hroots : (bad.image z).val ⊆ (P.coeff i).roots := by
    intro root hroot
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp
      (show root ∈ bad.image z from hroot)
    exact (Polynomial.mem_roots hcoeff).mpr
      (coeff_eval_eq_zero_of_contentRoot P (z seed)
        (Finset.mem_filter.mp hseed).2 i)
  calc
    bad.card = (bad.image z).card := hcard.symm
    _ ≤ (P.coeff i).natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ ≤ 72 := hdegree

private theorem exists_large_fiber
    {Seed Factor : Type} [DecidableEq Seed] [DecidableEq Factor]
    (source : Finset Seed) (target : Finset Factor) (assign : Seed → Factor)
    (hassign : ∀ seed ∈ source, assign seed ∈ target)
    {loss threshold : ℕ} (htarget : target.card ≤ loss)
    (hlarge : loss * threshold < source.card) :
    ∃ factor ∈ target,
      threshold < (source.filter fun seed => assign seed = factor).card := by
  by_contra hnone
  push Not at hnone
  have hmaps : Set.MapsTo assign (source : Set Seed) (target : Set Factor) :=
    fun seed hseed => hassign seed hseed
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum :
      (∑ factor ∈ target, (source.filter fun seed => assign seed = factor).card) ≤
        target.card * threshold := by
    calc
      _ ≤ ∑ _factor ∈ target, threshold :=
        Finset.sum_le_sum fun factor hfactor => hnone factor hfactor
      _ = target.card * threshold := by simp
  have : source.card ≤ loss * threshold := by
    rw [hpartition]
    exact hsum.trans (Nat.mul_le_mul_right threshold htarget)
  omega

open Classical in
/-- **Second `/11` selection contract.**

After at most `72` content roots, one normalized positive-`Y` factor occurs on
more than `threshold` seeds.  Its fraction-field image is separable, hence
coprime to its derivative.  `hfactorHeight` is the exact factor-height
inheritance contract supplied by the Cap72 total-degree argument. -/
theorem exists_fixed_separable_positiveYFactor
    {Seed : Type} [DecidableEq Seed]
    (P : BiPolynomial F) (hP : P ≠ 0) (hYDegree : P.natDegree ≤ 11)
    (hseparable : (fractionMap P).Separable)
    (hfactorHeight : ∀ H,
      H ∈ UniqueFactorizationMonoid.normalizedFactors P →
      0 < H.natDegree → ∀ i, (H.coeff i).natDegree ≤ 72)
    (seeds : Finset Seed) (z y : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (hroot : ∀ seed ∈ seeds, evalZY (z seed) (y seed) P = 0)
    (witnessIndex : ℕ) (hwitness : P.coeff witnessIndex ≠ 0)
    (hwitnessDegree : (P.coeff witnessIndex).natDegree ≤ 72)
    {threshold : ℕ} (hlarge : 11 * threshold + 72 < seeds.card) :
    ∃ H : BiPolynomial F,
      H ∈ UniqueFactorizationMonoid.normalizedFactors P ∧
      Irreducible H ∧
      0 < H.natDegree ∧
      H.natDegree ≤ 11 ∧
      (∀ i, (H.coeff i).natDegree ≤ 72) ∧
      H ∣ P ∧
      (fractionMap H).Separable ∧
      threshold <
        (seeds.filter fun seed => evalZY (z seed) (y seed) H = 0).card := by
  classical
  let good := seeds.filter fun seed => ¬ IsContentRoot P (z seed)
  have hcontentCard :
      (seeds.filter fun seed => IsContentRoot P (z seed)).card ≤ 72 :=
    card_contentRoots_le_seventyTwo P seeds z hz witnessIndex hwitness hwitnessDegree
  have hpartition :
      (seeds.filter fun seed => IsContentRoot P (z seed)).card + good.card =
        seeds.card := by
    simpa [good] using Finset.card_filter_add_card_filter_not
      (s := seeds) (p := fun seed => IsContentRoot P (z seed))
  have hgoodLarge : 11 * threshold < good.card := by omega
  have hchoices : ∀ seed, seed ∈ good →
      ∃ H ∈ positiveYFactors P, evalZY (z seed) (y seed) H = 0 := by
    intro seed hseed
    exact exists_positiveYFactor_of_evalZY_eq_zero P hP (z seed) (y seed)
      (hroot seed (Finset.mem_filter.mp hseed).1)
      (Finset.mem_filter.mp hseed).2
  let assign : Seed → BiPolynomial F := fun seed =>
    if hseed : seed ∈ good then Classical.choose (hchoices seed hseed) else 0
  have hassign : ∀ seed ∈ good, assign seed ∈ positiveYFactors P := by
    intro seed hseed
    simpa [assign, hseed] using (Classical.choose_spec (hchoices seed hseed)).1
  have hassignRoot : ∀ seed ∈ good, evalZY (z seed) (y seed) (assign seed) = 0 := by
    intro seed hseed
    simpa [assign, hseed] using (Classical.choose_spec (hchoices seed hseed)).2
  obtain ⟨H, hHpositive, hfiber⟩ := exists_large_fiber good (positiveYFactors P)
    assign hassign (card_positiveYFactors_le_natDegree P hP |>.trans hYDegree) hgoodLarge
  have hnormalized := (mem_positiveYFactors_iff.mp hHpositive).1
  have hpositive := (mem_positiveYFactors_iff.mp hHpositive).2
  have hdvd : H ∣ P := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hnormalized
  have hmapDvd : fractionMap H ∣ fractionMap P := by
    obtain ⟨K, rfl⟩ := hdvd
    exact ⟨fractionMap K, by simp [fractionMap, Polynomial.map_mul]⟩
  refine ⟨H, hnormalized,
    UniqueFactorizationMonoid.irreducible_of_normalized_factor H hnormalized,
    hpositive, (Polynomial.natDegree_le_of_dvd hdvd hP).trans hYDegree,
    hfactorHeight H hnormalized hpositive, hdvd,
    hseparable.of_dvd hmapDvd, ?_⟩
  refine lt_of_lt_of_le hfiber (Finset.card_le_card ?_)
  intro seed hseed
  have hgood := (Finset.mem_filter.mp hseed).1
  have hassigned := (Finset.mem_filter.mp hseed).2
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hgood).1,
    by simpa [hassigned] using hassignRoot seed hgood⟩

end

end ProximityPrize.SubmissionLower.SequentialFactorSelection
