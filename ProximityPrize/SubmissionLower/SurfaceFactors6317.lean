/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Genericity6317

/-!
# Global surface factors and the one-time content exception

We factor the primitive part in the outer variable `Y`.  Consequently every normalized factor
has positive `Y` degree; the discarded content is handled by one global exceptional set.  Both
the `Y` degrees and the corrected `Z+Y` grades are summed over the distinct factor set, so no
spurious cubic factor is introduced.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace SurfaceFactors6317

open Grading6317

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Distinct normalized factors of the primitive outer-`Y` part. -/
noncomputable def surfaceFactors (Q : F[X][X][Y]) : Finset F[X][X][Y] :=
  (UniqueFactorizationMonoid.normalizedFactors Q.primPart).toFinset

theorem mem_surfaceFactors_normalized {Q R : F[X][X][Y]}
    (hR : R ∈ surfaceFactors Q) :
    R ∈ UniqueFactorizationMonoid.normalizedFactors Q.primPart := by
  simpa [surfaceFactors] using hR

theorem irreducible_of_mem_surfaceFactors {Q R : F[X][X][Y]}
    (hR : R ∈ surfaceFactors Q) : Irreducible R :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor Q.primPart R
    (mem_surfaceFactors_normalized hR)

theorem dvd_primPart_of_mem_surfaceFactors {Q R : F[X][X][Y]}
    (hR : R ∈ surfaceFactors Q) : R ∣ Q.primPart :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    (mem_surfaceFactors_normalized hR)

theorem dvd_of_mem_surfaceFactors {Q R : F[X][X][Y]}
    (hR : R ∈ surfaceFactors Q) : R ∣ Q := by
  exact (dvd_primPart_of_mem_surfaceFactors hR).trans
    ⟨Polynomial.C Q.content, by
      rw [Polynomial.eq_C_content_mul_primPart]
      ring⟩

/-- Primitivity rules out an irreducible factor constant in `Y`. -/
theorem natDegree_pos_of_mem_surfaceFactors {Q R : F[X][X][Y]}
    (hR : R ∈ surfaceFactors Q) : 0 < R.natDegree := by
  by_contra hdeg
  have hdeg0 : R.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
  have hRC : R = Polynomial.C (R.coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (by omega)
  have hdiv : Polynomial.C (R.coeff 0) ∣ Q.primPart := by
    rw [← hRC]
    exact dvd_primPart_of_mem_surfaceFactors hR
  have hcontent : R.coeff 0 ∣ Q.primPart.content :=
    Polynomial.dvd_content_iff_C_dvd.mpr hdiv
  rw [Polynomial.content_primPart] at hcontent
  have hunitCoeff : IsUnit (R.coeff 0) := isUnit_iff_dvd_one.mpr hcontent
  have hunitR : IsUnit R := hRC ▸ hunitCoeff.map Polynomial.C
  exact (irreducible_of_mem_surfaceFactors hR).not_isUnit hunitR

theorem sum_natDegree_surfaceFactors_le (Q : F[X][X][Y]) :
    ∑ R ∈ surfaceFactors Q, R.natDegree ≤ Q.natDegree := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors Q.primPart
  have hs0 : (0 : F[X][X][Y]) ∉ s := by
    simpa [s] using UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q.primPart
  have hsumCount :
      ∑ R ∈ s.toFinset, R.natDegree ≤
        ∑ R ∈ s.toFinset, s.count R * R.natDegree := by
    apply Finset.sum_le_sum
    intro R hR
    exact Nat.le_mul_of_pos_left _ (Multiset.count_pos.mpr
      (Multiset.mem_toFinset.mp hR))
  have hcount : ∑ R ∈ s.toFinset, s.count R * R.natDegree =
      (s.map Polynomial.natDegree).sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count (s := s) (f := Polynomial.natDegree)).symm
  have hprodDegree : (s.map Polynomial.natDegree).sum = s.prod.natDegree := by
    exact (Polynomial.natDegree_multiset_prod hs0).symm
  have hassoc : Associated s.prod Q.primPart := by
    exact UniqueFactorizationMonoid.prod_normalizedFactors (Polynomial.primPart_ne_zero Q)
  have hprimDegree : s.prod.natDegree = Q.primPart.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassoc)
  calc
    ∑ R ∈ surfaceFactors Q, R.natDegree =
        ∑ R ∈ s.toFinset, R.natDegree := by simp [surfaceFactors, s]
    _ ≤ ∑ R ∈ s.toFinset, s.count R * R.natDegree := hsumCount
    _ = (s.map Polynomial.natDegree).sum := hcount
    _ = s.prod.natDegree := hprodDegree
    _ = Q.primPart.natDegree := hprimDegree
    _ = Q.natDegree := Polynomial.natDegree_primPart Q

theorem yzDegree_finset_prod
    {S : Finset F[X][X][Y]} (hne : ∀ R ∈ S, R ≠ 0) :
    yzDegree (∏ R ∈ S, R) = ∑ R ∈ S, yzDegree R := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [yzDegree, swapZX]
  | @insert R S hRS ih =>
      have hR : R ≠ 0 := hne R (by simp)
      have hS : (∏ T ∈ S, T) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun T hT ⇒ hne T (by simp [hT]))
      rw [Finset.prod_insert hRS, Finset.sum_insert hRS, yzDegree_mul hR hS]
      exact congrArg (yzDegree R + ·) (ih (fun T hT ⇒ hne T (by simp [hT])))

theorem prod_surfaceFactors_dvd (Q : F[X][X][Y]) :
    ∏ R ∈ surfaceFactors Q, R ∣ Q := by
  classical
  let s := UniqueFactorizationMonoid.normalizedFactors Q.primPart
  have hsubset : surfaceFactors Q ⊆ s.toFinset := by simp [surfaceFactors, s]
  have h₁ : ∏ R ∈ surfaceFactors Q, R ∣ ∏ R ∈ s.toFinset, R :=
    Finset.prod_dvd_prod_of_subset (f := id) hsubset
  have h₂ : ∏ R ∈ s.toFinset, R ∣ s.prod := by
    simpa using Multiset.toFinset_prod_dvd_prod s
  have h₃ : s.prod ∣ Q.primPart :=
    (UniqueFactorizationMonoid.prod_normalizedFactors
      (Polynomial.primPart_ne_zero Q)).dvd
  exact h₁.trans (h₂.trans (h₃.trans
    ⟨Polynomial.C Q.content, by
      rw [Polynomial.eq_C_content_mul_primPart]
      ring⟩))

theorem sum_yzDegree_surfaceFactors_le (Q : F[X][X][Y]) (hQ : Q ≠ 0) :
    ∑ R ∈ surfaceFactors Q, yzDegree R ≤ yzDegree Q := by
  classical
  let P := ∏ R ∈ surfaceFactors Q, R
  have hne : ∀ R ∈ surfaceFactors Q, R ≠ 0 :=
    fun R hR ⇒ (irreducible_of_mem_surfaceFactors hR).ne_zero
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  calc
    ∑ R ∈ surfaceFactors Q, yzDegree R = yzDegree P := by
      symm
      exact yzDegree_finset_prod hne
    _ ≤ yzDegree Q := yzDegree_le_of_dvd hP hQ (prod_surfaceFactors_dvd Q)

/-! ## The single global content exception -/

noncomputable def globalContentRootSet (Q : F[X][X][Y]) : Finset F :=
  Finset.univ.filter fun z ⇒ Bivariate.evalX z Q.content = 0

theorem globalContentRootSet_card_le_degreeX
    (Q : F[X][X][Y]) (hQ : Q ≠ 0) :
    (globalContentRootSet Q).card ≤ Bivariate.degreeX Q.content := by
  classical
  exact Bivariate.card_evalX_eq_zero_le_degreeX Q.content
    (by simpa [Polynomial.content_eq_zero_iff] using hQ) Finset.univ

theorem yzDegree_C_eq_degreeX (p : F[X][X]) :
    yzDegree (Polynomial.C p : F[X][X][Y]) = Bivariate.degreeX p := by
  classical
  simp [yzDegree, swapZX, Bivariate.totalDegree, Bivariate.natDegreeY_swap,
    Bivariate.natDegreeY]

theorem globalContent_degreeX_le_yzDegree
    (Q : F[X][X][Y]) (hQ : Q ≠ 0) :
    Bivariate.degreeX Q.content ≤ yzDegree Q := by
  have hcontent : Q.content ≠ 0 := by
    simpa [Polynomial.content_eq_zero_iff] using hQ
  rw [← yzDegree_C_eq_degreeX]
  exact yzDegree_le_of_dvd (Polynomial.C_ne_zero.mpr hcontent) hQ
    (Polynomial.C_content_dvd Q)

theorem globalContentRootSet_card_le_yzDegree
    (Q : F[X][X][Y]) (hQ : Q ≠ 0) :
    (globalContentRootSet Q).card ≤ yzDegree Q :=
  (globalContentRootSet_card_le_degreeX Q hQ).trans
    (globalContent_degreeX_le_yzDegree Q hQ)

/-- The global content and all distinct primitive surface factors share one `Z+Y` budget.
This is stronger than bounding the two pieces separately and prevents paying `DZ` twice. -/
theorem content_degreeX_add_sum_yzDegree_surfaceFactors_le
    (Q : F[X][X][Y]) (hQ : Q ≠ 0) :
    Bivariate.degreeX Q.content +
        ∑ R ∈ surfaceFactors Q, yzDegree R ≤ yzDegree Q := by
  classical
  let P := Polynomial.C Q.content * ∏ R ∈ surfaceFactors Q, R
  have hc : Q.content ≠ 0 := by
    simpa [Polynomial.content_eq_zero_iff] using hQ
  have hfac : (∏ R ∈ surfaceFactors Q, R) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun R hR ⇒
      (irreducible_of_mem_surfaceFactors hR).ne_zero
  have hP : P ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hfac
  have hPdiv : P ∣ Q := by
    have hprod : ∏ R ∈ surfaceFactors Q, R ∣ Q.primPart := by
      let s := UniqueFactorizationMonoid.normalizedFactors Q.primPart
      have h₁ : ∏ R ∈ surfaceFactors Q, R ∣ ∏ R ∈ s.toFinset, R := by
        apply Finset.prod_dvd_prod_of_subset (f := id)
        simp [surfaceFactors, s]
      have h₂ : ∏ R ∈ s.toFinset, R ∣ s.prod := by
        simpa using Multiset.toFinset_prod_dvd_prod s
      have h₃ : s.prod ∣ Q.primPart :=
        (UniqueFactorizationMonoid.prod_normalizedFactors
          (Polynomial.primPart_ne_zero Q)).dvd
      exact h₁.trans (h₂.trans h₃)
    obtain ⟨T, hT⟩ := hprod
    refine ⟨T, ?_⟩
    rw [P, hT, Polynomial.eq_C_content_mul_primPart]
    ring
  calc
    Bivariate.degreeX Q.content +
          ∑ R ∈ surfaceFactors Q, yzDegree R = yzDegree P := by
      rw [P, yzDegree_mul (Polynomial.C_ne_zero.mpr hc) hfac,
        yzDegree_C_eq_degreeX, yzDegree_finset_prod]
      exact fun R hR ⇒ (irreducible_of_mem_surfaceFactors hR).ne_zero
    _ ≤ yzDegree Q := yzDegree_le_of_dvd hP hQ hPdiv

end SurfaceFactors6317
end ProximityPrize.SubmissionLower
