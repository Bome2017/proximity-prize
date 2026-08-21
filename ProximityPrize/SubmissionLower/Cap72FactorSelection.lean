/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# Positive-Y factor selection for the Cap72 interpolant

This file contains the finite factor-selection step for a trivariate interpolant
`Q ∈ F[Z][X][Y]`.  It uses only normalized-factor APIs already available through
`TargetLower`.

There are three explicit losses:

* seeds where a degree-zero-in-`Y` factor vanishes after specializing `Z` are discarded;
* the remaining root at each seed is assigned to a positive-`Y` normalized factor;
* there are at most `natDegreeY Q`, hence at most `11` for Cap72, such factors.

The final theorem exposes the strict pigeonhole inequality `11 * threshold < goodSeeds.card`.
-/

namespace ProximityPrize.SubmissionLower.Cap72FactorSelection

open Polynomial

noncomputable section

variable {F : Type} [Field F] [DecidableEq F]

/- `TargetLower` exposes normalized-factor theory and the polynomial UFD instance, but not the
`FieldDivision` module which normally installs this normalization instance.  We reproduce that
instance locally (with the same leading-coefficient normalization) so normalized factors may be
used without adding a forbidden non-target import. -/
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

/-- Polynomials in `F[Z][X][Y]`, with `Y` the outer variable. -/
abbrev TriPolynomial (F : Type) [Semiring F] := Polynomial (Polynomial (Polynomial F))

/-- Specialize `Z := z`, then evaluate the outer variable at `p(X)`. -/
noncomputable def specializeAt (z : F) (p : F[X]) :
    TriPolynomial F →+* F[X] :=
  (Polynomial.evalRingHom p).comp
    (Polynomial.mapRingHom
      (Polynomial.mapRingHom (Polynomial.evalRingHom z)))

/-- Specialize only the innermost variable `Z := z`, leaving a polynomial in `X,Y`. -/
noncomputable def specializeZ (z : F) :
    TriPolynomial F →+* Polynomial (Polynomial F) :=
  Polynomial.mapRingHom
    (Polynomial.mapRingHom (Polynomial.evalRingHom z))

/-- Distinct positive-`Y` normalized factors of `Q`. -/
noncomputable def positiveYFactors (Q : TriPolynomial F) : Finset (TriPolynomial F) :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun factor => 0 < factor.natDegree)

/-- A seed is lost to content when a normalized factor constant in `Y` becomes the zero
polynomial in `X` after `Z := z`.  This predicate is independent of the proposed root `p(X)`. -/
def IsContentSpecializationRoot (Q : TriPolynomial F) (z : F) : Prop :=
  ∃ factor ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    factor.natDegree = 0 ∧
      (factor.coeff 0).map (Polynomial.evalRingHom z) = 0

/-- A content-specialization root kills the entire `Z`-specialization of `Q`. -/
theorem specializeZ_eq_zero_of_contentSpecializationRoot
    (Q : TriPolynomial F) (z : F)
    (hcontent : IsContentSpecializationRoot Q z) :
    specializeZ z Q = 0 := by
  classical
  obtain ⟨factor, hfactor, hdegree, hfactorZero⟩ := hcontent
  obtain ⟨quotient, hQ⟩ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
  have hfactorConstant : factor = Polynomial.C (factor.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hspecializedFactor : specializeZ z factor = 0 := by
    rw [hfactorConstant]
    simpa [specializeZ] using hfactorZero
  rw [hQ, map_mul, hspecializedFactor, zero_mul]

/-- Consequently every fixed `(Y,X)` coefficient of `Q`, viewed as a polynomial in `Z`,
vanishes at every content-specialization root. -/
theorem coeff_eval_eq_zero_of_contentSpecializationRoot
    (Q : TriPolynomial F) (z : F)
    (hcontent : IsContentSpecializationRoot Q z) (yDegree xDegree : ℕ) :
    ((Q.coeff yDegree).coeff xDegree).eval z = 0 := by
  have hzero := specializeZ_eq_zero_of_contentSpecializationRoot Q z hcontent
  have hcoeff := congrArg
    (fun P : Polynomial (Polynomial F) => (P.coeff yDegree).coeff xDegree) hzero
  simpa [specializeZ] using hcoeff

open Classical in
/-- Content roots in a seed set are bounded by any nonzero `(Y,X)` coefficient of `Q`.

The injectivity assumption is exactly what is needed to convert a bound on distinct field roots
into a bound on seeds.  In the IRS application, `z` is the seed itself (or an embedding of it). -/
theorem card_contentSpecializationRoots_le_natDegree_coeff
    {Seed : Type} [DecidableEq Seed]
    (Q : TriPolynomial F) (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed)) (yDegree xDegree : ℕ)
    (hcoeff : (Q.coeff yDegree).coeff xDegree ≠ 0) :
    (seeds.filter fun seed => IsContentSpecializationRoot Q (z seed)).card ≤
      ((Q.coeff yDegree).coeff xDegree).natDegree := by
  classical
  let badSeeds := seeds.filter fun seed => IsContentSpecializationRoot Q (z seed)
  let witness : F[X] := (Q.coeff yDegree).coeff xDegree
  have hbadSubset : (badSeeds : Set Seed) ⊆ (seeds : Set Seed) := by
    intro seed hseed
    exact (Finset.mem_filter.mp hseed).1
  have hzinj : Set.InjOn z (badSeeds : Set Seed) := hz.mono hbadSubset
  have himageCard : (badSeeds.image z).card = badSeeds.card :=
    Finset.card_image_iff.mpr hzinj
  have hroots : (badSeeds.image z).val ⊆ witness.roots := by
    intro root hroot
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp
      (show root ∈ badSeeds.image z from hroot)
    have hcontent : IsContentSpecializationRoot Q (z seed) :=
      (Finset.mem_filter.mp hseed).2
    exact (Polynomial.mem_roots (by simpa [witness] using hcoeff)).mpr
      (by simpa [witness] using
        (coeff_eval_eq_zero_of_contentSpecializationRoot Q (z seed) hcontent
          yDegree xDegree))
  calc
    badSeeds.card = (badSeeds.image z).card := himageCard.symm
    _ ≤ witness.natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ = ((Q.coeff yDegree).coeff xDegree).natDegree := rfl

open Classical in
/-- Cap72-ready form of the content-root bound.  Assembly only has to exhibit one nonzero
`(Y,X)` coefficient of `Q` and prove that its `Z`-degree is at most `72`. -/
theorem card_contentSpecializationRoots_le_seventyTwo
    {Seed : Type} [DecidableEq Seed]
    (Q : TriPolynomial F) (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed)) (yDegree xDegree : ℕ)
    (hcoeff : (Q.coeff yDegree).coeff xDegree ≠ 0)
    (hdegree : ((Q.coeff yDegree).coeff xDegree).natDegree ≤ 72) :
    (seeds.filter fun seed => IsContentSpecializationRoot Q (z seed)).card ≤ 72 :=
  (card_contentSpecializationRoots_le_natDegree_coeff Q seeds z hz yDegree xDegree hcoeff).trans
    hdegree

lemma mem_positiveYFactors_iff {Q factor : TriPolynomial F} :
    factor ∈ positiveYFactors Q ↔
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        0 < factor.natDegree := by
  classical
  simp [positiveYFactors]

/-- The number of distinct normalized factors with positive `Y`-degree is at most the
`Y`-degree of the original polynomial.  No separability assumption is needed. -/
theorem card_positiveYFactors_le_natDegree (Q : TriPolynomial F) (hQ : Q ≠ 0) :
    (positiveYFactors Q).card ≤ Q.natDegree := by
  classical
  let factors : Multiset (TriPolynomial F) :=
    UniqueFactorizationMonoid.normalizedFactors Q
  let positive : Finset (TriPolynomial F) :=
    factors.toFinset.filter (fun factor => 0 < factor.natDegree)
  have hpositive : positive = positiveYFactors Q := by
    simp [positive, positiveYFactors, factors]
  have hpositiveSum : positive.card ≤ ∑ factor ∈ positive, factor.natDegree := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun factor hfactor => by
      exact (Finset.mem_filter.mp hfactor).2
  have hsubset : positive ⊆ factors.toFinset := by
    intro factor hfactor
    exact (Finset.mem_filter.mp hfactor).1
  have hsumSubset :
      (∑ factor ∈ positive, factor.natDegree) ≤
        ∑ factor ∈ factors.toFinset, factor.natDegree :=
    Finset.sum_le_sum_of_subset hsubset
  have hsumCount :
      (∑ factor ∈ factors.toFinset, factor.natDegree) ≤
        ∑ factor ∈ factors.toFinset, factors.count factor * factor.natDegree := by
    refine Finset.sum_le_sum ?_
    intro factor hfactor
    have hmem : factor ∈ factors := Multiset.mem_toFinset.mp hfactor
    exact Nat.le_mul_of_pos_left factor.natDegree (Multiset.count_pos.mpr hmem)
  have hcounted :
      (∑ factor ∈ factors.toFinset, factors.count factor * factor.natDegree) =
        (factors.map Polynomial.natDegree).sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count
        (s := factors) (f := fun factor => factor.natDegree)).symm
  have hzero : (0 : TriPolynomial F) ∉ factors := by
    simpa [factors] using
      (UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q)
  have hdegreeProduct :
      (factors.map Polynomial.natDegree).sum = factors.prod.natDegree := by
    exact (Polynomial.natDegree_multiset_prod factors hzero).symm
  have hassociated : Associated factors.prod Q := by
    simpa [factors] using
      (UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ)
  have hdegree : factors.prod.natDegree = Q.natDegree := by
    apply Polynomial.natDegree_eq_of_degree_eq
    exact Polynomial.degree_eq_degree_of_associated hassociated
  rw [← hpositive]
  exact hpositiveSum.trans
    (hsumSubset.trans (hsumCount.trans_eq (hcounted.trans (hdegreeProduct.trans hdegree))))

/-- Cap72's outer degree bound leaves at most eleven positive-`Y` factors. -/
theorem card_positiveYFactors_le_eleven
    (Q : TriPolynomial F) (hQ : Q ≠ 0) (hdegree : Q.natDegree ≤ 11) :
    (positiveYFactors Q).card ≤ 11 :=
  (card_positiveYFactors_le_natDegree Q hQ).trans hdegree

/-- A root of `Q` which is not a content-specialization root belongs to a positive-`Y`
normalized factor. -/
theorem exists_positiveYFactor_of_specialize_eq_zero
    (Q : TriPolynomial F) (hQ : Q ≠ 0) (z : F) (p : F[X])
    (hroot : specializeAt z p Q = 0)
    (hcontent : ¬ IsContentSpecializationRoot Q z) :
    ∃ factor ∈ positiveYFactors Q, specializeAt z p factor = 0 := by
  classical
  let factors : Multiset (TriPolynomial F) :=
    UniqueFactorizationMonoid.normalizedFactors Q
  let phi : TriPolynomial F →+* F[X] := specializeAt z p
  have hassociated : Associated factors.prod Q := by
    simpa [factors] using
      (UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ)
  have hmappedAssociated : Associated (phi factors.prod) (phi Q) :=
    Associated.map (phi : TriPolynomial F →* F[X]) hassociated
  have hproduct : phi factors.prod = 0 :=
    hmappedAssociated.eq_zero_iff.mpr (by simpa [phi] using hroot)
  have hmapProduct : (factors.map phi).prod = 0 := by
    simpa [map_multiset_prod] using hproduct
  have hzeroMem : (0 : F[X]) ∈ factors.map phi :=
    (Multiset.prod_eq_zero_iff.mp hmapProduct)
  obtain ⟨factor, hfactor, hfactorZero⟩ := Multiset.mem_map.mp hzeroMem
  have hfactorNormalized :
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
    simpa [factors] using hfactor
  have hfactorEval : specializeAt z p factor = 0 := by
    simpa [phi] using hfactorZero
  have hfactorDegree : 0 < factor.natDegree := by
    by_contra hnotPositive
    have hdegreeZero : factor.natDegree = 0 := Nat.eq_zero_of_not_pos hnotPositive
    apply hcontent
    refine ⟨factor, hfactorNormalized, hdegreeZero, ?_⟩
    have hconstant : factor = Polynomial.C (factor.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdegreeZero
    rw [hconstant] at hfactorEval
    simpa [specializeAt] using hfactorEval
  exact ⟨factor, mem_positiveYFactors_iff.mpr
    ⟨hfactorNormalized, hfactorDegree⟩, hfactorEval⟩

/-- Finite pigeonhole with an explicit target-cardinality loss. -/
private theorem exists_large_fiber_of_maps_to
    {Seed Factor : Type} [DecidableEq Seed] [DecidableEq Factor]
    (source : Finset Seed) (target : Finset Factor) (assign : Seed → Factor)
    (hassign : ∀ seed ∈ source, assign seed ∈ target)
    {loss threshold : ℕ}
    (htarget : target.card ≤ loss)
    (hlarge : loss * threshold < source.card) :
    ∃ factor ∈ target,
      threshold < (source.filter fun seed => assign seed = factor).card := by
  by_contra hnone
  push Not at hnone
  have hmaps : Set.MapsTo assign (source : Set Seed) (target : Set Factor) := by
    intro seed hseed
    exact hassign seed hseed
  have hpartition :
      source.card = ∑ factor ∈ target,
        (source.filter fun seed => assign seed = factor).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hsumBound :
      (∑ factor ∈ target,
        (source.filter fun seed => assign seed = factor).card) ≤
          target.card * threshold := by
    calc
      (∑ factor ∈ target,
          (source.filter fun seed => assign seed = factor).card) ≤
          ∑ _factor ∈ target, threshold := by
            exact Finset.sum_le_sum fun factor hfactor => hnone factor hfactor
      _ = target.card * threshold := by simp
  have hsourceBound : source.card ≤ loss * threshold := by
    rw [hpartition]
    exact hsumBound.trans (Nat.mul_le_mul_right threshold htarget)
  omega

open Classical in
/-- **Cap72 positive-factor selection.**

After explicitly removing content-specialization roots, a family larger than
`11 * threshold` contains more than `threshold` seeds killed by one fixed irreducible
positive-`Y` normalized factor. -/
theorem exists_fixed_positiveYFactor
    {Seed : Type} [DecidableEq Seed]
    (Q : TriPolynomial F) (hQ : Q ≠ 0) (hdegree : Q.natDegree ≤ 11)
    (seeds : Finset Seed) (z : Seed → F) (p : Seed → F[X])
    (hroot : ∀ seed ∈ seeds, specializeAt (z seed) (p seed) Q = 0)
    (hcontent : ∀ seed ∈ seeds, ¬ IsContentSpecializationRoot Q (z seed))
    {threshold : ℕ} (hlarge : 11 * threshold < seeds.card) :
    ∃ factor,
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
      Irreducible factor ∧
      0 < factor.natDegree ∧
      threshold <
        (seeds.filter fun seed =>
          specializeAt (z seed) (p seed) factor = 0).card := by
  classical
  have hexists : ∀ seed, seed ∈ seeds →
      ∃ factor ∈ positiveYFactors Q,
        specializeAt (z seed) (p seed) factor = 0 := by
    intro seed hseed
    exact exists_positiveYFactor_of_specialize_eq_zero Q hQ (z seed) (p seed)
      (hroot seed hseed) (hcontent seed hseed)
  let assign : Seed → TriPolynomial F := fun seed =>
    if hseed : seed ∈ seeds then Classical.choose (hexists seed hseed) else 0
  have hassignMem : ∀ seed ∈ seeds, assign seed ∈ positiveYFactors Q := by
    intro seed hseed
    simpa [assign, hseed] using (Classical.choose_spec (hexists seed hseed)).1
  have hassignRoot : ∀ seed ∈ seeds,
      specializeAt (z seed) (p seed) (assign seed) = 0 := by
    intro seed hseed
    simpa [assign, hseed] using (Classical.choose_spec (hexists seed hseed)).2
  obtain ⟨factor, hfactorPositive, hfiber⟩ :=
    exists_large_fiber_of_maps_to seeds (positiveYFactors Q) assign
      hassignMem (card_positiveYFactors_le_eleven Q hQ hdegree) hlarge
  have hnormalized :
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
    (mem_positiveYFactors_iff.mp hfactorPositive).1
  have hirreducible : Irreducible factor :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor factor hnormalized
  refine ⟨factor, hnormalized, hirreducible,
    (mem_positiveYFactors_iff.mp hfactorPositive).2, ?_⟩
  refine lt_of_lt_of_le hfiber ?_
  apply Finset.card_le_card
  intro seed hseed
  have hsource : seed ∈ seeds := (Finset.mem_filter.mp hseed).1
  have hassigned : assign seed = factor := (Finset.mem_filter.mp hseed).2
  apply Finset.mem_filter.mpr
  refine ⟨hsource, ?_⟩
  simpa [hassigned] using hassignRoot seed hsource

open Classical in
/-- Variant of `exists_fixed_positiveYFactor` which performs the content-root discard itself.

The hypothesis records the content loss as an explicit natural number.  Thus the only losses in
the selection step are `contentLoss` discarded seeds and the factor-count multiplier `11`. -/
theorem exists_fixed_positiveYFactor_after_discard
    {Seed : Type} [DecidableEq Seed]
    (Q : TriPolynomial F) (hQ : Q ≠ 0) (hdegree : Q.natDegree ≤ 11)
    (seeds : Finset Seed) (z : Seed → F) (p : Seed → F[X])
    (hroot : ∀ seed ∈ seeds, specializeAt (z seed) (p seed) Q = 0)
    {contentLoss threshold : ℕ}
    (hcontentLoss :
      (seeds.filter fun seed => IsContentSpecializationRoot Q (z seed)).card ≤
        contentLoss)
    (hlarge : 11 * threshold + contentLoss < seeds.card) :
    ∃ factor,
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
      Irreducible factor ∧
      0 < factor.natDegree ∧
      threshold <
        (seeds.filter fun seed =>
          specializeAt (z seed) (p seed) factor = 0).card := by
  classical
  let goodSeeds := seeds.filter fun seed =>
    ¬ IsContentSpecializationRoot Q (z seed)
  have hpartition :
      (seeds.filter fun seed => IsContentSpecializationRoot Q (z seed)).card +
          goodSeeds.card = seeds.card := by
    simpa [goodSeeds] using
      (Finset.card_filter_add_card_filter_not
        (s := seeds) (p := fun seed => IsContentSpecializationRoot Q (z seed)))
  have hgoodLarge : 11 * threshold < goodSeeds.card := by
    omega
  have hgoodRoot : ∀ seed ∈ goodSeeds,
      specializeAt (z seed) (p seed) Q = 0 := by
    intro seed hseed
    have hseedFilter : seed ∈ seeds.filter fun candidate =>
        ¬ IsContentSpecializationRoot Q (z candidate) := by
      simpa [goodSeeds] using hseed
    exact hroot seed (Finset.mem_filter.mp hseedFilter).1
  have hgoodContent : ∀ seed ∈ goodSeeds,
      ¬ IsContentSpecializationRoot Q (z seed) := by
    intro seed hseed
    exact (Finset.mem_filter.mp hseed).2
  obtain ⟨factor, hnormalized, hirreducible, hpositive, hfiber⟩ :=
    exists_fixed_positiveYFactor Q hQ hdegree goodSeeds z p
      hgoodRoot hgoodContent hgoodLarge
  refine ⟨factor, hnormalized, hirreducible, hpositive,
    lt_of_lt_of_le hfiber ?_⟩
  apply Finset.card_le_card
  intro seed hseed
  have hgood : seed ∈ goodSeeds := (Finset.mem_filter.mp hseed).1
  have hfactorRoot := (Finset.mem_filter.mp hseed).2
  have hgoodFilter : seed ∈ seeds.filter fun candidate =>
      ¬ IsContentSpecializationRoot Q (z candidate) := by
    simpa [goodSeeds] using hgood
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hgoodFilter).1, hfactorRoot⟩

open Classical in
/-- Fully combined Cap72 selection contract.

One nonzero `(Y,X)` coefficient of `Q` of `Z`-degree at most `72` accounts for every content
root.  The remaining seeds lose only the factor-count multiplier `11`. -/
theorem exists_fixed_positiveYFactor_cap72
    {Seed : Type} [DecidableEq Seed]
    (Q : TriPolynomial F) (hQ : Q ≠ 0) (hYDegree : Q.natDegree ≤ 11)
    (seeds : Finset Seed) (z : Seed → F) (p : Seed → F[X])
    (hz : Set.InjOn z (seeds : Set Seed))
    (hroot : ∀ seed ∈ seeds, specializeAt (z seed) (p seed) Q = 0)
    (yDegree xDegree : ℕ)
    (hcoeff : (Q.coeff yDegree).coeff xDegree ≠ 0)
    (hcoeffDegree : ((Q.coeff yDegree).coeff xDegree).natDegree ≤ 72)
    {threshold : ℕ} (hlarge : 11 * threshold + 72 < seeds.card) :
    ∃ factor,
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
      Irreducible factor ∧
      0 < factor.natDegree ∧
      threshold <
        (seeds.filter fun seed =>
          specializeAt (z seed) (p seed) factor = 0).card := by
  exact exists_fixed_positiveYFactor_after_discard Q hQ hYDegree seeds z p hroot
    (contentLoss := 72)
    (card_contentSpecializationRoots_le_seventyTwo Q seeds z hz
      yDegree xDegree hcoeff hcoeffDegree)
    hlarge

end

end ProximityPrize.SubmissionLower.Cap72FactorSelection
