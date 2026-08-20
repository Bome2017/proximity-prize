/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.HeavyCell6317

/-!
# The two independent gradings of the BCHKS interpolation polynomial

The interpolation polynomial is stored as `F[Z][X][Y]`.  Its enormous `X` degree must not be
charged to Appendix A: the Hensel argument uses the `Z+Y` grading.  This file makes that grading
explicit by swapping `Z` and `X` inside every `Y` coefficient and then taking ordinary bivariate
total degree.  The second grading records the middle-`X` degree used only in the generic-point
avoidance argument.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace Grading6317

variable {F : Type} [Field F]

/-- Swap `Z` and `X` in every coefficient of the outer `Y` polynomial. -/
noncomputable def swapZX (R : F[X][X][Y]) : F[X][X][Y] :=
  R.map (Polynomial.Bivariate.swap (R := F)).toRingHom

@[simp] theorem swapZX_coeff (R : F[X][X][Y]) (j : ℕ) :
    (swapZX R).coeff j = Polynomial.Bivariate.swap (R.coeff j) := by
  simp [swapZX]

@[simp] theorem swapZX_zero : swapZX (0 : F[X][X][Y]) = 0 := by
  simp [swapZX]

@[simp] theorem swapZX_mul (R S : F[X][X][Y]) :
    swapZX (R * S) = swapZX R * swapZX S := by
  simp [swapZX]

theorem swapZX_ne_zero {R : F[X][X][Y]} (hR : R ≠ 0) : swapZX R ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff
    (Polynomial.Bivariate.swap (R := F)).injective).mpr hR

/-- `Z+Y` degree, with the middle interpolation variable `X` assigned weight zero. -/
noncomputable def yzDegree (R : F[X][X][Y]) : ℕ :=
  Bivariate.totalDegree (swapZX R)

theorem yzDegree_coeff_le (R : F[X][X][Y]) {j : ℕ} (hj : j ∈ R.support) :
    Bivariate.degreeX (R.coeff j) + j ≤ yzDegree R := by
  have hmap : j ∈ (swapZX R).support := by
    rw [Polynomial.support_map_of_injective R
      (Polynomial.Bivariate.swap (R := F)).injective]
    exact hj
  have h := Bivariate.coeff_totalDegree_le (swapZX R) hmap
  simpa [yzDegree, Bivariate.natDegreeY, Bivariate.natDegreeY_swap] using h

theorem yzDegree_mul {R S : F[X][X][Y]} (hR : R ≠ 0) (hS : S ≠ 0) :
    yzDegree (R * S) = yzDegree R + yzDegree S := by
  rw [yzDegree, swapZX_mul,
    Bivariate.totalDegree_mul (swapZX_ne_zero hR) (swapZX_ne_zero hS)]
  rfl

theorem yzDegree_le_of_dvd {R Q : F[X][X][Y]}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hdiv : R ∣ Q) :
    yzDegree R ≤ yzDegree Q := by
  obtain ⟨S, rfl⟩ := hdiv
  have hS : S ≠ 0 := by
    intro h
    exact hQ (by simp [h])
  rw [yzDegree_mul hR hS]
  exact Nat.le_add_right _ _

theorem xDegree_le_of_dvd {R Q : F[X][X][Y]}
    (hR : R ≠ 0) (hQ : Q ≠ 0) (hdiv : R ∣ Q) :
    Bivariate.degreeX R ≤ Bivariate.degreeX Q := by
  obtain ⟨S, rfl⟩ := hdiv
  have hS : S ≠ 0 := by
    intro h
    exact hQ (by simp [h])
  rw [Bivariate.degreeX_mul R S hR hS]
  exact Nat.le_add_right _ _

/-! ## The concrete interpolation box -/

theorem targetInterpolant_xDegree_lt
    [DecidableEq F] {domain : Fin targetN ↪ F} {u₀ u₁ : Fin targetN → F}
    (I : TargetInterpolant domain u₀ u₁) :
    Bivariate.degreeX I.polynomial < targetDX := by
  classical
  unfold Bivariate.degreeX
  rw [Finset.sup_lt_iff (by norm_num [targetDX])]
  intro j hj
  have hjle : j ≤ I.polynomial.natDegree :=
    Polynomial.le_natDegree_of_mem_supp hj
  have hjDY : j < targetDY := hjle.trans_lt I.Y_degree
  exact (Nat.le_add_right _ _).trans_lt (I.X_weight j hjDY)

theorem targetInterpolant_yzDegree_lt
    [DecidableEq F] {domain : Fin targetN ↪ F} {u₀ u₁ : Fin targetN → F}
    (I : TargetInterpolant domain u₀ u₁) :
    yzDegree I.polynomial < targetDZ := by
  classical
  unfold yzDegree Bivariate.totalDegree
  rw [Finset.sup_lt_iff (by norm_num [targetDZ])]
  intro j hjmap
  have hj : j ∈ I.polynomial.support := by
    rw [Polynomial.support_map_of_injective I.polynomial
      (Polynomial.Bivariate.swap (R := F)).injective] at hjmap
    exact hjmap
  have hjle : j ≤ I.polynomial.natDegree :=
    Polynomial.le_natDegree_of_mem_supp hj
  have hjDY : j < targetDY := hjle.trans_lt I.Y_degree
  have hinner : Bivariate.degreeX (I.polynomial.coeff j) + j < targetDZ := by
    unfold Bivariate.degreeX
    rw [Finset.sup_add_distrib, Finset.sup_lt_iff (by norm_num [targetDZ])]
    intro i hi
    exact I.ZY_weight i j hjDY
  simpa [swapZX_coeff, Bivariate.natDegreeY, Bivariate.natDegreeY_swap] using hinner

theorem targetInterpolant_factor_grades
    [DecidableEq F] {domain : Fin targetN ↪ F} {u₀ u₁ : Fin targetN → F}
    (I : TargetInterpolant domain u₀ u₁)
    {R : F[X][X][Y]} (hR : R ≠ 0) (hdiv : R ∣ I.polynomial) :
    Bivariate.degreeX R ≤ targetDX ∧ yzDegree R ≤ targetDZ := by
  refine ⟨(xDegree_le_of_dvd hR I.polynomial_ne_zero hdiv).trans ?_,
    (yzDegree_le_of_dvd hR I.polynomial_ne_zero hdiv).trans ?_⟩
  · exact (targetInterpolant_xDegree_lt I).le
  · exact (targetInterpolant_yzDegree_lt I).le

theorem targetInterpolant_factor_hensel_grade
    [DecidableEq F] {domain : Fin targetN ↪ F} {u₀ u₁ : Fin targetN → F}
    (I : TargetInterpolant domain u₀ u₁)
    {R : F[X][X][Y]} (hR : R ≠ 0) (hdiv : R ∣ I.polynomial) :
    ∀ j ∈ R.support, Bivariate.degreeX (R.coeff j) + j ≤ targetDZ := by
  intro j hj
  exact (yzDegree_coeff_le R hj).trans
    (targetInterpolant_factor_grades I hR hdiv).2

end Grading6317
end ProximityPrize.SubmissionLower
