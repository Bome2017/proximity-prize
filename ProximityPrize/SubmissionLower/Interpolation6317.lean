/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Decode6317

/-!
# The target trivariate interpolation kernel

This is the linear-algebra core of BCHKS Lemma 3.1 at the concrete prize parameters.  The
unknowns are exactly the triangular monomials counted in `BCHKS6317`; the equations are the
coefficients in `Z` of every required mixed Hasse derivative after shifting to
`(x, u₀(x)+Z u₁(x))`.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open Polynomial
open scoped BigOperators ENNReal NNReal

section Interpolation

variable {F : Type} [Field F]

/-- A single triangular monomial `X^i Y^j Z^h`, represented in `F[Z][X][Y]`. -/
noncomputable def targetGSBasis (q : TargetCoefficientIndex) :
    Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.monomial q.1.1
    (Polynomial.monomial q.2.1.1 (Polynomial.monomial q.2.2.1 1))

/-- Assemble a trivariate polynomial from its triangular coefficient vector. -/
noncomputable def targetGSPolyLinearMap :
    (TargetCoefficientIndex → F) →ₗ[F]
      Polynomial (Polynomial (Polynomial F)) :=
  Finsupp.linearCombination F (targetGSBasis (F := F)) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F TargetCoefficientIndex).symm.toLinearMap

noncomputable def targetGSPoly (c : TargetCoefficientIndex → F) :
    Polynomial (Polynomial (Polynomial F)) :=
  targetGSPolyLinearMap c

/-- Coefficient extraction after a bivariate shift is an `F`-linear functional. -/
noncomputable def targetGSEvalConstraint
    (x y : Polynomial F) (r s d : ℕ) :
    Polynomial (Polynomial (Polynomial F)) →ₗ[F] F where
  toFun Q := ((((Polynomial.Bivariate.shift Q x y).coeff s).coeff r).coeff d)
  map_add' Q R := by simp [Polynomial.Bivariate.shift]
  map_smul' a Q := by simp [Polynomial.Bivariate.shift]

/-- The complete homogeneous interpolation system for one pair of received words. -/
noncomputable def targetGSConstraintMap
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F) :
    (TargetCoefficientIndex → F) →ₗ[F] (TargetConstraintIndex → F) :=
  LinearMap.pi (fun q =>
    targetGSEvalConstraint
      (Polynomial.C (domain q.1))
      (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))
      q.2.2.1.1 q.2.1.1 q.2.2.2.1 ∘ₗ
    targetGSPolyLinearMap)

/-- A nonzero triangular coefficient vector satisfying every interpolation equation. -/
structure TargetGSKernelWitness
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F) where
  coefficients : TargetCoefficientIndex → F
  coefficients_ne_zero : coefficients ≠ 0
  constraints : targetGSConstraintMap domain u₀ u₁ coefficients = 0

/-- Dimension surplus gives a nonzero interpolation-kernel vector over every field. -/
theorem exists_targetGSKernelWitness
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F) :
    Nonempty (TargetGSKernelWitness domain u₀ u₁) := by
  have hfinrank :
      Module.finrank F (TargetConstraintIndex → F) <
        Module.finrank F (TargetCoefficientIndex → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      target_constraints_lt_coefficients
  have hker : LinearMap.ker (targetGSConstraintMap domain u₀ u₁) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨⟨c, hc0, hc⟩⟩

theorem targetGSConstraintMap_apply
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F)
    (c : TargetCoefficientIndex → F) (q : TargetConstraintIndex) :
    targetGSConstraintMap domain u₀ u₁ c q =
      ((((Polynomial.Bivariate.shift (targetGSPoly c)
        (Polynomial.C (domain q.1))
        (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))).coeff
          q.2.1.1).coeff q.2.2.1.1).coeff q.2.2.2.1) := by
  rfl

theorem targetGSPoly_eq_sum (c : TargetCoefficientIndex → F) :
    targetGSPoly c = ∑ q : TargetCoefficientIndex, c q • targetGSBasis q := by
  unfold targetGSPoly targetGSPolyLinearMap
  rw [Finsupp.linearCombination_eq_fintype_linearCombination,
    Fintype.linearCombination_apply]

/-- Reading a supported monomial coefficient recovers the source vector entry. -/
theorem targetGSPoly_coeff_index (c : TargetCoefficientIndex → F)
    (q : TargetCoefficientIndex) :
    ((((targetGSPoly c).coeff q.1.1).coeff q.2.1.1).coeff q.2.2.1) = c q := by
  classical
  rw [targetGSPoly_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    targetGSBasis, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single q]
  · simp
  · intro r _ hrq
    by_cases hj : r.1.1 = q.1.1
    · by_cases hi : r.2.1.1 = q.2.1.1
      · have hh : r.2.2.1 ≠ q.2.2.1 := by
          intro hh
          apply hrq
          rcases r with ⟨rj, ri, rh⟩
          rcases q with ⟨qj, qi, qh⟩
          simp only at hj hi hh ⊢
          subst qj
          have hi' : ri = qi := Fin.ext hi
          subst qi
          exact Sigma.ext (Fin.ext hh) (by rfl)
        simp [hj, hi, hh]
      · simp [hj, hi]
    · simp [hj]
  · simp

/-- The assembled interpolation polynomial is genuinely nonzero. -/
theorem targetGSPoly_ne_zero
    {c : TargetCoefficientIndex → F} (hc : c ≠ 0) : targetGSPoly c ≠ 0 := by
  intro hzero
  apply hc
  funext q
  have hcoeff := targetGSPoly_coeff_index c q
  rw [hzero] at hcoeff
  simpa using hcoeff.symm

private theorem targetInnerMonomial_shift_coeff
    (a h : ℕ) (x : F) (r : ℕ) :
    (((Polynomial.monomial a (Polynomial.monomial h 1) :
      Polynomial (Polynomial F)).comp
        (Polynomial.X + Polynomial.C (Polynomial.C x))).coeff r) =
      Polynomial.monomial h (x ^ (a - r) * (a.choose r : F)) := by
  rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.monomial_mul_C, one_mul]

private theorem targetOuterAffine_map (x y₀ y₁ : F) :
    Polynomial.map
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x)))
      (Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁))) =
      Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)) := by
  simp [Polynomial.coe_compRingHom_apply]

/-- Closed form of a shifted basis coefficient. -/
theorem targetGSBasis_shift_coeff_formula (q : TargetCoefficientIndex)
    (x y₀ y₁ : F) (r s : ℕ) :
    ((Polynomial.Bivariate.shift (targetGSBasis (F := F) q)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff s).coeff r =
    Polynomial.monomial q.2.2.1
      (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F) *
        (q.1.1.choose s : F)) *
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1 - s) := by
  classical
  unfold targetGSBasis Polynomial.Bivariate.shift
  rw [Polynomial.monomial_comp, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, targetOuterAffine_map]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.coeff_mul_C]
  rw [Polynomial.coe_compRingHom_apply, targetInnerMonomial_shift_coeff]
  rw [← Polynomial.C_eq_natCast]
  calc
    Polynomial.monomial q.2.2.1
        (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F)) *
        ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1 - s) *
          Polynomial.C (q.1.1.choose s : F)) =
      (Polynomial.monomial q.2.2.1
        (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F)) *
          Polynomial.C (q.1.1.choose s : F)) *
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1 - s) := by ring
    _ = Polynomial.monomial q.2.2.1
        (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F) *
          (q.1.1.choose s : F)) *
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1 - s) := by
      rw [Polynomial.monomial_mul_C]

theorem targetGSBasis_shift_coeff_natDegree_le (q : TargetCoefficientIndex)
    (x y₀ y₁ : F) (r s : ℕ) :
    (((Polynomial.Bivariate.shift (targetGSBasis (F := F) q)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff s).coeff r).natDegree ≤
      q.2.2.1 + (q.1.1 - s) := by
  rw [targetGSBasis_shift_coeff_formula]
  have hlinear :
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁).natDegree ≤ 1 := by
    rw [show Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁ =
      Polynomial.C y₁ * Polynomial.X + Polynomial.C y₀ by ring]
    exact Polynomial.natDegree_linear_le
  have hpow := Polynomial.natDegree_pow_le_of_le (q.1.1 - s) hlinear
  have hmono := Polynomial.natDegree_monomial_le
    (m := q.2.2.1)
    (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F) * (q.1.1.choose s : F))
  calc
    (Polynomial.monomial q.2.2.1
        (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F) *
          (q.1.1.choose s : F)) *
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1 - s)).natDegree
        ≤ (Polynomial.monomial q.2.2.1
          (x ^ (q.2.1.1 - r) * (q.2.1.1.choose r : F) *
            (q.1.1.choose s : F))).natDegree +
          ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^
            (q.1.1 - s)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ q.2.2.1 + (q.1.1 - s) := by
      exact add_le_add hmono (by simpa only [mul_one] using hpow)

theorem targetGSPoly_shift_coeff_eq_sum
    (c : TargetCoefficientIndex → F) (x y : Polynomial F) (r s : ℕ) :
    ((Polynomial.Bivariate.shift (targetGSPoly c) x y).coeff s).coeff r =
      ∑ q : TargetCoefficientIndex, c q •
        ((Polynomial.Bivariate.shift (targetGSBasis (F := F) q) x y).coeff s).coeff r := by
  ext d
  change targetGSEvalConstraint x y r s d (targetGSPoly c) = _
  rw [targetGSPoly_eq_sum, map_sum]
  simp only [map_smul]
  change (∑ q : TargetCoefficientIndex,
      c q • targetGSEvalConstraint x y r s d (targetGSBasis q)) =
    (∑ q ∈ Finset.univ, c q •
      ((Polynomial.Bivariate.shift (targetGSBasis q) x y).coeff s).coeff r).coeff d
  rw [Polynomial.finsetSum_coeff]
  rfl

/-- The triangular `j+h<DZ` support ensures that the shifted `(r,s)` coefficient has
`Z`-degree strictly below `DZ-s`. -/
theorem targetGSPoly_shift_coeff_natDegree_lt
    (c : TargetCoefficientIndex → F) (x y₀ y₁ : F) (r s : ℕ)
    (hs : s < targetM) :
    (((Polynomial.Bivariate.shift (targetGSPoly c)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff s).coeff r).natDegree <
      targetDZ - s := by
  rw [targetGSPoly_shift_coeff_eq_sum]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun q _ => ?_) ?_
  · refine (Polynomial.natDegree_smul_le _ _).trans
      (targetGSBasis_shift_coeff_natDegree_le q x y₀ y₁ r s)
  · have hj : q.1.1 < targetDZ := by
      have := q.1.2
      norm_num [targetDY, targetDZ] at this ⊢
      omega
    have hh := q.2.2.2
    norm_num [targetDZ] at hh ⊢
    omega

/-- Every mixed Hasse coefficient required by multiplicity `targetM` vanishes identically as
a polynomial in `Z`. -/
theorem targetGSKernelWitness_shift_vanish
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F)
    (w : TargetGSKernelWitness domain u₀ u₁) :
    ∀ i r s, r + s < targetM →
      ((Polynomial.Bivariate.shift (targetGSPoly w.coefficients)
        (Polynomial.C (domain i))
        (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff s).coeff r = 0 := by
  intro i r s hrs
  have hs : s < targetM := by omega
  apply Polynomial.ext
  intro d
  by_cases hd : d < targetDZ - s
  · let q : TargetConstraintIndex :=
      (i, ⟨⟨s, hs⟩,
        (⟨r, by omega⟩, ⟨d, hd⟩)⟩)
    have hzero := congrFun w.constraints q
    simp only [Pi.zero_apply] at hzero
    rw [targetGSConstraintMap_apply] at hzero
    exact hzero
  · have hdeg := targetGSPoly_shift_coeff_natDegree_lt w.coefficients
      (domain i) (u₀ i) (u₁ i) r s hs
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (by omega))

/-! ## Degree and multiplicity certificate -/

/-- The outer (`Y`) degree is below the concrete `DY`. -/
theorem targetGSPoly_natDegree_lt_DY (c : TargetCoefficientIndex → F) :
    (targetGSPoly c).natDegree < targetDY := by
  rw [targetGSPoly_eq_sum]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun q _ => ?_)
    (by norm_num [targetDY])
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  unfold targetGSBasis
  exact (Polynomial.natDegree_monomial_le _).trans (by
    have := q.1.2
    norm_num [targetDY] at this ⊢
    omega)

/-- At every supported `Y` index, the `X` degree satisfies `i + k j < DX`. -/
theorem targetGSPoly_coeff_X_weight_lt
    (c : TargetCoefficientIndex → F) (j : ℕ) (hj : j < targetDY) :
    ((targetGSPoly c).coeff j).natDegree + targetK * j < targetDX := by
  have hgap : 0 < targetDX - targetK * j := by
    norm_num [targetDX, targetK, targetDY] at hj ⊢
    omega
  have hdegree : ((targetGSPoly c).coeff j).natDegree ≤
      targetDX - targetK * j - 1 := by
    rw [targetGSPoly_eq_sum, Polynomial.finsetSum_coeff]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q _
    by_cases hqj : q.1.1 = j
    · rw [Polynomial.coeff_smul, targetGSBasis, Polynomial.coeff_monomial,
        if_pos hqj]
      refine (Polynomial.natDegree_smul_le _ _).trans
        ((Polynomial.natDegree_monomial_le _).trans ?_)
      have hi := q.2.1.2
      norm_num [targetDX, targetK, targetDY] at hj hi ⊢
      omega
    · simp [targetGSBasis, Polynomial.coeff_smul,
        Polynomial.coeff_monomial, hqj]
  norm_num [targetDX, targetK] at hdegree hgap ⊢
  omega

/-- Every `X^i Y^j` coefficient has `Z` degree satisfying `h+j<DZ`. -/
theorem targetGSPoly_coeff_ZY_weight_lt
    (c : TargetCoefficientIndex → F) (i j : ℕ) (hj : j < targetDY) :
    ((((targetGSPoly c).coeff j).coeff i).natDegree + j) < targetDZ := by
  have hgap : 0 < targetDZ - j := by
    norm_num [targetDZ, targetDY] at hj ⊢
    omega
  have hdegree : (((targetGSPoly c).coeff j).coeff i).natDegree ≤
      targetDZ - j - 1 := by
    rw [targetGSPoly_eq_sum, Polynomial.finsetSum_coeff,
      Polynomial.finsetSum_coeff]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q _
    by_cases hqj : q.1.1 = j
    · by_cases hqi : q.2.1.1 = i
      · rw [Polynomial.coeff_smul, Polynomial.coeff_smul, targetGSBasis,
          Polynomial.coeff_monomial, if_pos hqj,
          Polynomial.coeff_monomial, if_pos hqi]
        refine (Polynomial.natDegree_smul_le _ _).trans
          ((Polynomial.natDegree_monomial_le _).trans ?_)
        have hh := q.2.2.2
        norm_num [targetDZ, targetDY] at hj hh ⊢
        omega
      · simp [targetGSBasis, Polynomial.coeff_smul,
          Polynomial.coeff_monomial, hqj, hqi]
    · simp [targetGSBasis, Polynomial.coeff_smul,
        Polynomial.coeff_monomial, hqj]
  norm_num [targetDZ] at hdegree hgap ⊢
  omega

/-- Hasse vanishing is equivalent to multiplicity at least `targetM` for the nonzero
interpolant. -/
theorem targetGSPoly_multiplicity_of_shift_vanish
    [DecidableEq F] {c : TargetCoefficientIndex → F}
    (hQ : targetGSPoly c ≠ 0)
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F)
    (hvan : ∀ i r s, r + s < targetM →
      ((Polynomial.Bivariate.shift (targetGSPoly c)
        (Polynomial.C (domain i))
        (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff s).coeff r = 0) :
    ∀ i, targetM ≤ Polynomial.Bivariate.rootMultiplicity
      (targetGSPoly c)
      (Polynomial.C (domain i))
      (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
  intro i
  let g := Polynomial.Bivariate.shift (targetGSPoly c)
    (Polynomial.C (domain i))
    (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))
  have hg : ∀ r s, r + s < targetM →
      Polynomial.Bivariate.coeff g r s = 0 := by
    intro r s hrs
    exact hvan i r s hrs
  have H := (Polynomial.Bivariate.rootMultiplicity₀_ge_iff g targetM).mp hg
  have hgne : g ≠ 0 := Polynomial.Bivariate.shift_ne_zero _ _ _ hQ
  have hroot : Polynomial.Bivariate.rootMultiplicity₀ g ≠ none :=
    Polynomial.Bivariate.rootMultiplicity₀_ne_none g hgne
  change (some targetM : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity₀ g
  cases hr : Polynomial.Bivariate.rootMultiplicity₀ g with
  | none => exact False.elim (hroot hr)
  | some r =>
      have hmr : targetM ≤ r := H r (by simp only [hr, Option.mem_def])
      simpa only [hr, Option.some_le_some] using hmr

/-- Complete concrete interpolation output used by the factor/capture argument. -/
structure TargetInterpolant [DecidableEq F]
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F) where
  polynomial : Polynomial (Polynomial (Polynomial F))
  polynomial_ne_zero : polynomial ≠ 0
  Y_degree : polynomial.natDegree < targetDY
  X_weight : ∀ j, j < targetDY →
    (polynomial.coeff j).natDegree + targetK * j < targetDX
  ZY_weight : ∀ i j, j < targetDY →
    ((polynomial.coeff j).coeff i).natDegree + j < targetDZ
  shift_vanishing : ∀ i r s, r + s < targetM →
    ((Polynomial.Bivariate.shift polynomial
      (Polynomial.C (domain i))
      (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff s).coeff r = 0
  multiplicity : ∀ i, targetM ≤ Polynomial.Bivariate.rootMultiplicity polynomial
    (Polynomial.C (domain i))
    (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))

/-- BCHKS Lemma 3.1 specialized to the exact integer degree box selected for the prize. -/
theorem exists_targetInterpolant [DecidableEq F]
    (domain : Fin targetN ↪ F) (u₀ u₁ : Fin targetN → F) :
    Nonempty (TargetInterpolant domain u₀ u₁) := by
  let w := Classical.choice (exists_targetGSKernelWitness domain u₀ u₁)
  have hQ := targetGSPoly_ne_zero w.coefficients_ne_zero
  exact ⟨{
    polynomial := targetGSPoly w.coefficients
    polynomial_ne_zero := hQ
    Y_degree := targetGSPoly_natDegree_lt_DY w.coefficients
    X_weight := targetGSPoly_coeff_X_weight_lt w.coefficients
    ZY_weight := targetGSPoly_coeff_ZY_weight_lt w.coefficients
    shift_vanishing := targetGSKernelWitness_shift_vanish domain u₀ u₁ w
    multiplicity := targetGSPoly_multiplicity_of_shift_vanish hQ domain u₀ u₁
      (targetGSKernelWitness_shift_vanish domain u₀ u₁ w) }⟩

end Interpolation

end ProximityPrize.SubmissionLower
