/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.RootVanishing6317

/-!
# Primitive specializations and positive-degree factors

The factor argument is run on the primitive part of the `Y`-polynomial obtained after
specializing `X`.  This is essential: retaining its `F[Z]`-content makes the published
Appendix-A weight estimate false.  The roots of the removed content are kept in a separate
exceptional set and paid for once.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

section PositiveFactors

variable {F : Type} [Field F]

/-- The irreducible factors with positive degree in the outer variable. -/
noncomputable def positiveDegreeFactors (p : Polynomial (Polynomial F)) :
    Multiset (Polynomial (Polynomial F)) :=
  (UniqueFactorizationMonoid.normalizedFactors p).filter
    (fun q => 0 < q.natDegree)

theorem mem_positiveDegreeFactors_degree_pos {p H : Polynomial (Polynomial F)}
    (hH : H ∈ positiveDegreeFactors p) : 0 < H.natDegree := by
  simpa [positiveDegreeFactors] using Multiset.of_mem_filter hH

theorem mem_normalizedFactors_of_mem_positiveDegreeFactors
    {p H : Polynomial (Polynomial F)} (hH : H ∈ positiveDegreeFactors p) :
    H ∈ UniqueFactorizationMonoid.normalizedFactors p :=
  Multiset.mem_of_mem_filter hH

theorem irreducible_of_mem_positiveDegreeFactors
    {p H : Polynomial (Polynomial F)} (hH : H ∈ positiveDegreeFactors p) :
    Irreducible H :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor p H
    (mem_normalizedFactors_of_mem_positiveDegreeFactors hH)

/-- The sum of the positive factor degrees is at most the degree of the polynomial.
Multiplicity is retained in the multiset, as required by the aggregate BCHKS count. -/
theorem sum_natDegree_positiveDegreeFactors_le (p : Polynomial (Polynomial F)) :
    (positiveDegreeFactors p |>.map Polynomial.natDegree).sum ≤ p.natDegree := by
  classical
  by_cases hp : p = 0
  · simp [positiveDegreeFactors, hp]
  let s := UniqueFactorizationMonoid.normalizedFactors p
  have hs0 : (0 : Polynomial (Polynomial F)) ∉ s := by
    simpa [s] using UniqueFactorizationMonoid.zero_notMem_normalizedFactors p
  have hdeg : (s.map Polynomial.natDegree).sum = p.natDegree := by
    rw [← Polynomial.natDegree_multiset_prod hs0]
    exact Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated
        (UniqueFactorizationMonoid.prod_normalizedFactors hp))
  have hsub : positiveDegreeFactors p ≤ s := by
    simpa [positiveDegreeFactors, s] using
      (Multiset.filter_le (fun q : Polynomial (Polynomial F) => 0 < q.natDegree) s)
  obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hsub
  rw [ht, Multiset.map_add, Multiset.sum_add] at hdeg
  omega

/-- Distinct positive factors are no more numerous than their total degree. -/
theorem card_toFinset_positiveDegreeFactors_le_sum (p : Polynomial (Polynomial F)) :
    (positiveDegreeFactors p).toFinset.card ≤
      (positiveDegreeFactors p |>.map Polynomial.natDegree).sum := by
  classical
  calc
    (positiveDegreeFactors p).toFinset.card ≤ (positiveDegreeFactors p).card :=
      Multiset.toFinset_card_le
    _ = (positiveDegreeFactors p |>.map (fun _ => 1)).sum := by simp
    _ ≤ (positiveDegreeFactors p |>.map Polynomial.natDegree).sum := by
      apply Multiset.sum_le_sum
      intro H hH
      exact mem_positiveDegreeFactors_degree_pos hH

theorem card_toFinset_positiveDegreeFactors_le_natDegree
    (p : Polynomial (Polynomial F)) :
    (positiveDegreeFactors p).toFinset.card ≤ p.natDegree :=
  (card_toFinset_positiveDegreeFactors_le_sum p).trans
    (sum_natDegree_positiveDegreeFactors_le p)

/-- Forgetting multiplicities can only decrease the sum of the positive factor degrees. -/
theorem sum_natDegree_toFinset_positiveDegreeFactors_le (p : Polynomial (Polynomial F)) :
    ∑ H ∈ (positiveDegreeFactors p).toFinset, H.natDegree ≤ p.natDegree := by
  classical
  let s := positiveDegreeFactors p
  calc
    ∑ H ∈ s.toFinset, H.natDegree ≤
        ∑ H ∈ s.toFinset, s.count H * H.natDegree := by
      apply Finset.sum_le_sum
      intro H hH
      exact Nat.le_mul_of_pos_left _ (Multiset.count_pos.mpr
        (Multiset.mem_toFinset.mp hH))
    _ = (s.map Polynomial.natDegree).sum := by
      simpa [Nat.nsmul_eq_mul] using
        (Finset.sum_multiset_map_count (s := s) (f := Polynomial.natDegree)).symm
    _ ≤ p.natDegree := sum_natDegree_positiveDegreeFactors_le p

end PositiveFactors

section Content

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Evaluate a polynomial in `Y` with coefficients in `F[Z]` at `(y,z)`. -/
noncomputable def evalZY (p : Polynomial (Polynomial F)) (z y : F) : F :=
  (p.map (Polynomial.evalRingHom z)).eval y

/-- Scalars annihilating the `F[Z]`-content of a specialized `Y`-polynomial. -/
noncomputable def contentRootSet (p : Polynomial (Polynomial F)) : Finset F :=
  Finset.univ.filter fun z => p.content.eval z = 0

theorem contentRootSet_card_le (p : Polynomial (Polynomial F))
    (hp : p.content ≠ 0) :
    (contentRootSet p).card ≤ p.content.natDegree := by
  classical
  have hsub : contentRootSet p ⊆ p.content.roots.toFinset := by
    intro z hz
    have hz0 : p.content.eval z = 0 := (Finset.mem_filter.mp hz).2
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hz0)
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le (m := p.content.roots)).trans
      (Polynomial.card_roots' p.content))

theorem evalZY_primPart_eq_zero_of_not_contentRoot
    (p : Polynomial (Polynomial F)) (z y : F)
    (hp : evalZY p z y = 0) (hz : z ∉ contentRootSet p) :
    evalZY p.primPart z y = 0 := by
  classical
  have hc : p.content.eval z ≠ 0 := by
    simpa [contentRootSet] using hz
  have hfac := congrArg (fun q : Polynomial (Polynomial F) => evalZY q z y)
    p.eq_C_content_mul_primPart
  simp only [evalZY, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
    Polynomial.coe_evalRingHom, Polynomial.eval_C] at hfac
  exact (mul_eq_zero.mp (hfac ▸ hp)).resolve_left hc

/-- A zero of a primitive polynomial is caught by a positive-degree normalized factor.
The apparently harmless positivity conclusion is precisely where removing the content is used. -/
theorem exists_positive_factor_of_evalZY_primPart_eq_zero
    (p : Polynomial (Polynomial F)) (z y : F)
    (hroot : evalZY p.primPart z y = 0) :
    ∃ H ∈ positiveDegreeFactors p.primPart, evalZY H z y = 0 := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors p.primPart
  have hp0 : p.primPart ≠ 0 := Polynomial.primPart_ne_zero p
  have hassoc : Associated s.prod p.primPart := by
    exact UniqueFactorizationMonoid.prod_normalizedFactors hp0
  let φ : Polynomial (Polynomial F) →+* F :=
    (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  have hφp : φ p.primPart = 0 := by simpa [φ, evalZY] using hroot
  have hφprod : φ s.prod = 0 := hassoc.map φ |>.eq_zero_iff.mpr hφp
  have hprod : (s.map φ).prod = 0 := by simpa [map_multiset_prod] using hφprod
  obtain ⟨H, hHs, hH0⟩ := Multiset.prod_eq_zero_iff.mp hprod |>
    (fun h => Multiset.mem_map.mp h)
  refine ⟨H, ?_, ?_⟩
  · have hpos : 0 < H.natDegree := by
      by_contra hdeg
      have hdeg0 : H.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
      have hHC : H = Polynomial.C (H.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero (by omega)
      have hHirr : Irreducible H :=
        UniqueFactorizationMonoid.irreducible_of_normalized_factor p.primPart H hHs
      have hcoeffUnit : IsUnit (H.coeff 0) := by
        have hCdvd : Polynomial.C (H.coeff 0) ∣ p.primPart := by
          rw [← hHC]
          exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHs
        have hcontent : H.coeff 0 ∣ p.primPart.content :=
          Polynomial.dvd_content_iff_C_dvd.mpr hCdvd
        rw [Polynomial.content_primPart] at hcontent
        exact isUnit_iff_dvd_one.mpr hcontent
      exact hHirr.not_isUnit (hHC ▸ hcoeffUnit.map Polynomial.C)
    simpa [positiveDegreeFactors, hHs, hpos]
  · simpa [φ, evalZY] using hH0

/-- Primitive/content cover in the exact form used to assign every decoded scalar to a cell. -/
theorem content_or_positive_factor_of_evalZY_eq_zero
    (p : Polynomial (Polynomial F)) (z y : F)
    (hroot : evalZY p z y = 0) :
    z ∈ contentRootSet p ∨
      ∃ H ∈ positiveDegreeFactors p.primPart, evalZY H z y = 0 := by
  classical
  by_cases hz : z ∈ contentRootSet p
  · exact Or.inl hz
  · exact Or.inr (exists_positive_factor_of_evalZY_primPart_eq_zero p z y
      (evalZY_primPart_eq_zero_of_not_contentRoot p z y hroot hz))

end Content

end ProximityPrize.SubmissionLower
