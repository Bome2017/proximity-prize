/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.FactorCount6317

/-!
# The affine-branch endgame for one BCHKS factor cell

This file contains no Hensel or factorization assumptions.  It isolates the last, purely
Reed--Solomon step: once every decoded polynomial in a cell is the specialization of one affine
polynomial branch `v₀ + Z v₁`, the MCA row-failure condition assigns each scalar injectively to a
coordinate.  Thus at most `n` scalars remain after the algebraic heavy-cell threshold.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped BigOperators ENNReal NNReal

section AffineBranch

/-- Evaluation of an affine polynomial family at a scalar. -/
noncomputable def affinePolynomial (v₀ v₁ : Polynomial IRSProfile.Field)
    (γ : IRSProfile.Field) : Polynomial IRSProfile.Field :=
  v₀ + Polynomial.C γ * v₁

theorem affinePolynomial_eval (v₀ v₁ : Polynomial IRSProfile.Field)
    (γ x : IRSProfile.Field) :
    (affinePolynomial v₀ v₁ γ).eval x = v₀.eval x + γ * v₁.eval x := by
  simp [affinePolynomial]

theorem affinePolynomial_degree_lt
    {v₀ v₁ : Polynomial IRSProfile.Field}
    (h₀ : v₀.degree < IRSProfile.baseDimension)
    (h₁ : v₁.degree < IRSProfile.baseDimension)
    (γ : IRSProfile.Field) :
    (affinePolynomial v₀ v₁ γ).degree < IRSProfile.baseDimension := by
  unfold affinePolynomial
  exact (Polynomial.degree_add_le _ _).trans_lt
    (max_lt h₀ ((Polynomial.degree_mul_le _ _).trans_lt (by simpa using h₁)))

/-- If a received row is not in the projected RS code but `v` is a valid RS polynomial, some
support coordinate witnesses a discrepancy with `v`. -/
lemma exists_support_discrepancy_of_row_failure
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {S : Finset IRSProfile.Index} {j : Fin 2}
    (v : Polynomial IRSProfile.Field)
    (hv : v.degree < IRSProfile.baseDimension)
    (hfail : LinearCode.projectedWord (U j) S ∉
      LinearCode.projectedCodeSubmod IRSProfile.baseCode S) :
    ∃ i ∈ S, U j i ≠ v.eval (IRSProfile.domain i) := by
  classical
  by_contra h
  push Not at h
  apply hfail
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain v, ?_, ?_⟩
  · exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt hv
  · funext i
    simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using (h i.1 i.2)

/-- A decoded scalar lying on a fixed affine polynomial branch has a coordinate at which the
corresponding affine discrepancy has nonzero slope and vanishes. -/
lemma affine_coordinate_witness_of_decode_on_branch
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {γ : IRSProfile.Field} (d : TargetDecode U γ)
    (v₀ v₁ : Polynomial IRSProfile.Field)
    (hv₀ : v₀.degree < IRSProfile.baseDimension)
    (hv₁ : v₁.degree < IRSProfile.baseDimension)
    (hbranch : d.polynomial = affinePolynomial v₀ v₁ γ) :
    ∃ i : IRSProfile.Index,
      (U 1 i - v₁.eval (IRSProfile.domain i)) ≠ 0 ∧
      (U 1 i - v₁.eval (IRSProfile.domain i)) * γ +
        (U 0 i - v₀.eval (IRSProfile.domain i)) = 0 := by
  classical
  obtain ⟨j, hj⟩ := d.row_failure
  let v : Fin 2 → Polynomial IRSProfile.Field := fun r => if r = 0 then v₀ else v₁
  have hv : (v j).degree < IRSProfile.baseDimension := by
    fin_cases j <;> simp [v, hv₀, hv₁]
  obtain ⟨i, hi, hneq⟩ := exists_support_discrepancy_of_row_failure v hv hj
  have hagree := d.agreement i hi
  rw [hbranch, affinePolynomial_eval] at hagree
  have hroot :
      (U 1 i - v₁.eval (IRSProfile.domain i)) * γ +
        (U 0 i - v₀.eval (IRSProfile.domain i)) = 0 := by
    linear_combination hagree
  refine ⟨i, ?_, hroot⟩
  intro hslope
  have hintercept : U 0 i - v₀.eval (IRSProfile.domain i) = 0 := by
    simpa [hslope] using hroot
  have hrow0 : U 0 i = v₀.eval (IRSProfile.domain i) := sub_eq_zero.mp hintercept
  have hrow1 : U 1 i = v₁.eval (IRSProfile.domain i) := sub_eq_zero.mp hslope
  fin_cases j
  · exact hneq (by simpa [v] using hrow0)
  · exact hneq (by simpa [v] using hrow1)

/-- The one-coordinate-per-scalar bound for a complete affine branch. -/
theorem card_cell_le_targetN_of_affine_branch
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (E : Finset IRSProfile.Field)
    (decode : ∀ γ : {γ // γ ∈ E}, TargetDecode U γ.1)
    (v₀ v₁ : Polynomial IRSProfile.Field)
    (hv₀ : v₀.degree < IRSProfile.baseDimension)
    (hv₁ : v₁.degree < IRSProfile.baseDimension)
    (hbranch : ∀ γ : {γ // γ ∈ E},
      (decode γ).polynomial = affinePolynomial v₀ v₁ γ.1) :
    E.card ≤ targetN := by
  let slope : IRSProfile.Index → IRSProfile.Field := fun i =>
    U 1 i - v₁.eval (IRSProfile.domain i)
  let intercept : IRSProfile.Index → IRSProfile.Field := fun i =>
    U 0 i - v₀.eval (IRSProfile.domain i)
  apply target_factor_exception_card_le E slope intercept
  intro γ hγ
  let z : {z // z ∈ E} := ⟨γ, hγ⟩
  simpa [slope, intercept, z] using
    affine_coordinate_witness_of_decode_on_branch (decode z) v₀ v₁ hv₀ hv₁ (hbranch z)

/-- A cell is bounded by `core + n` as soon as crossing `core` forces one global affine branch. -/
theorem card_cell_le_core_add_targetN
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (E : Finset IRSProfile.Field) (core : ℕ)
    (decode : ∀ γ : {γ // γ ∈ E}, TargetDecode U γ.1)
    (hheavy : core < E.card →
      ∃ v₀ v₁ : Polynomial IRSProfile.Field,
        v₀.degree < IRSProfile.baseDimension ∧
        v₁.degree < IRSProfile.baseDimension ∧
        ∀ γ : {γ // γ ∈ E},
          (decode γ).polynomial = affinePolynomial v₀ v₁ γ.1) :
    E.card ≤ core + targetN := by
  by_cases hsmall : E.card ≤ core
  · omega
  · obtain ⟨v₀, v₁, hv₀, hv₁, hbranch⟩ := hheavy (Nat.lt_of_not_ge hsmall)
    exact (card_cell_le_targetN_of_affine_branch U E decode v₀ v₁ hv₀ hv₁ hbranch).trans
      (Nat.le_add_left targetN core)

end AffineBranch

end ProximityPrize.SubmissionLower
