/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Interpolation6317

/-!
# Specialization and divisibility of every target decode

The interpolant is constructed over `F[Z]`.  This file proves that specialization commutes with
the mixed Hasse shifts, and then gives the usual Guruswami--Sudan root-count argument.  The
strict numerical inequality used here is
`DX = 41,243,289 < 222 * 186,199 = 41,336,178`.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open Polynomial
open scoped BigOperators ENNReal NNReal

section Specialization

variable {F : Type} [Field F]

/-- Evaluate the `Z` coefficients of a trivariate polynomial. -/
noncomputable def specializeZ (Q : Polynomial (Polynomial (Polynomial F))) (γ : F) :
    Polynomial (Polynomial F) :=
  Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))

@[simp] theorem specializeZ_zero (γ : F) : specializeZ (0 :
    Polynomial (Polynomial (Polynomial F))) γ = 0 := by
  simp [specializeZ]

/-- Specialization commutes with shifting the `X,Y` variables, coefficient by coefficient. -/
theorem specializeZ_shift_coeff
    (Q : Polynomial (Polynomial (Polynomial F))) (γ x y₀ y₁ : F) (r s : ℕ) :
    Polynomial.Bivariate.coeff
        (Polynomial.Bivariate.shift (specializeZ Q γ) x (y₀ + γ * y₁)) r s =
      ((((Polynomial.Bivariate.shift Q
        (Polynomial.C x)
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff s).coeff r).eval γ) := by
  unfold specializeZ Polynomial.Bivariate.coeff Polynomial.Bivariate.shift
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq, add_mul]
      | monomial m a =>
          simp [Polynomial.coe_compRingHom_apply, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_pow]

/-- Local form of the standard `(1,k-1)` weighted evaluation-degree lemma. -/
theorem natDegree_eval_le_weighted
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (k : ℕ)
    (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) := by
  have hdeg : (Q.eval P).natDegree ≤
      (Q.support.image (fun j => (Q.coeff j).natDegree + (k - 1) * j)).sup id := by
    rw [Polynomial.eval_eq_sum_range]
    refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
    intro j hj
    by_cases hc : Q.coeff j = 0
    · simp [hc]
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have hpj := Polynomial.natDegree_pow_le_of_le j hP
      refine le_trans (Nat.add_le_add le_rfl hpj) ?_
      have hjQ : j ∈ Q.support := Polynomial.mem_support_iff.mpr hc
      exact Finset.le_sup (f := fun t => (Q.coeff t).natDegree + (k - 1) * t) hjQ
  unfold Polynomial.Bivariate.natWeightedDegree
  simpa only [one_mul] using hdeg

/-- The specialized interpolant retains the strict weighted `X,Y` degree bound. -/
theorem specializeZ_weightedDegree_lt
    [DecidableEq F] {domain : Fin targetN ↪ F} {u₀ u₁ : Fin targetN → F}
    (I : TargetInterpolant domain u₀ u₁) (γ : F) :
    Polynomial.Bivariate.natWeightedDegree (specializeZ I.polynomial γ)
      1 (targetK - 1) < targetDX := by
  unfold Polynomial.Bivariate.natWeightedDegree
  rw [Finset.sup_lt_iff (by norm_num [targetDX])]
  intro j hj
  have hmapdeg : ((specializeZ I.polynomial γ).coeff j).natDegree ≤
      (I.polynomial.coeff j).natDegree := by
    rw [specializeZ, Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le
  have hjdeg : j ≤ (specializeZ I.polynomial γ).natDegree :=
    Polynomial.le_natDegree_of_mem_supp hj
  have houter : (specializeZ I.polynomial γ).natDegree ≤ I.polynomial.natDegree :=
    Polynomial.natDegree_map_le
  have hjDY : j < targetDY := lt_of_le_of_lt (hjdeg.trans houter) I.Y_degree
  have hx := I.X_weight j hjDY
  norm_num [targetK] at hx ⊢
  omega

/-! ## Multiplicity roots force specialization divisibility -/

/-- Origin-order vanishing is preserved by substitution into a polynomial with zero constant
term. -/
theorem X_pow_dvd_eval_of_origin_order
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (m : ℕ)
    (hQ : ∀ r s, r + s < m → Polynomial.Bivariate.coeff Q r s = 0)
    (hP : P.coeff 0 = 0) :
    Polynomial.X ^ m ∣ Q.eval P := by
  have hPpow : ∀ s : ℕ, Polynomial.X ^ s ∣ P ^ s :=
    fun s => pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hP) s
  have hterm : ∀ r s : ℕ, (Q.coeff s).coeff r ≠ 0 →
      Polynomial.X ^ m ∣ Polynomial.monomial r ((Q.coeff s).coeff r) * P ^ s := by
    intro r s hrs
    have hrsdiv : Polynomial.X ^ (r + s) ∣
        Polynomial.monomial r ((Q.coeff s).coeff r) * P ^ s := by
      simp only [pow_add]
      exact mul_dvd_mul (by simp [← Polynomial.C_mul_X_pow_eq_monomial]) (hPpow s)
    exact dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt fun h => hrs (hQ r s h))) hrsdiv
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine Finset.dvd_sum fun s hs => ?_
  rw [(Q.coeff s).as_sum_range_C_mul_X_pow]
  simp only [Finset.sum_mul, Polynomial.C_mul_X_pow_eq_monomial]
  classical
  exact Finset.dvd_sum fun r hr => if hz : (Q.coeff s).coeff r = 0 then by simp [hz]
    else hterm r s hz

/-- Evaluation after a bivariate shift is the shifted univariate evaluation. -/
theorem eval_shifted_eq_shifted_eval_6317
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (x y : F) :
    let Qsh := Polynomial.Bivariate.shift Q x y
    let Psh := P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y
    Qsh.eval Psh = (Q.eval P).comp (Polynomial.X + Polynomial.C x) := by
  induction Q using Polynomial.induction_on' <;> aesop

def TargetHasOrderAt (Q : Polynomial (Polynomial F)) (x y : F) (m : ℕ) : Prop :=
  ∀ r s, r + s < m →
    Polynomial.Bivariate.coeff (Polynomial.Bivariate.shift Q x y) r s = 0

/-- A bivariate order condition gives the corresponding univariate root multiplicity. -/
theorem orderAt_eval_ge_6317
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (x : F) (m : ℕ)
    (h : TargetHasOrderAt Q x (P.eval x) m) :
    Q.eval P = 0 ∨ m ≤ (Q.eval P).rootMultiplicity x := by
  let Qsh := Polynomial.Bivariate.shift Q x (P.eval x)
  let Psh := P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C (P.eval x)
  have hdiv : Polynomial.X ^ m ∣ Qsh.eval Psh := by
    apply X_pow_dvd_eval_of_origin_order
    · exact h
    · simp [Psh, Polynomial.coeff_zero_eq_eval_zero]
  have hshift : Qsh.eval Psh = (Q.eval P).comp (Polynomial.X + Polynomial.C x) := by
    exact eval_shifted_eq_shifted_eval_6317 Q P x (P.eval x)
  have hrootdiv : (Polynomial.X - Polynomial.C x) ^ m ∣ Q.eval P := by
    exact Polynomial.X_sub_C_pow_dvd_iff.mpr (hshift ▸ hdiv)
  by_cases hz : Q.eval P = 0
  · exact Or.inl hz
  · exact Or.inr ((Polynomial.le_rootMultiplicity_iff hz).mpr hrootdiv)

/-- More distinct roots with multiplicity `m` than the degree force the zero polynomial. -/
theorem eq_zero_of_many_multiplicity_roots
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (domain : ι ↪ F) (R : Polynomial F) (m : ℕ) (A : Finset ι)
    (hroots : ∀ i ∈ A, m ≤ R.rootMultiplicity (domain i))
    (hdeg : R.natDegree < m * A.card) : R = 0 := by
  classical
  have hsum : ∑ x ∈ A.image domain, R.rootMultiplicity x ≤ R.natDegree := by
    have hfactor : ∏ x ∈ A.image domain,
        (Polynomial.X - Polynomial.C x) ^ R.rootMultiplicity x ∣ R := by
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro x hx y hy hxy
        exact IsCoprime.pow (Polynomial.irreducible_X_sub_C x |>
          fun hirr => hirr.coprime_iff_not_dvd.mpr fun hdvd => hxy <| by
            simpa [sub_eq_iff_eq_add] using Polynomial.dvd_iff_isRoot.mp hdvd)
      · exact fun x hx => R.pow_rootMultiplicity_dvd x
    have hle := Polynomial.natDegree_le_of_dvd hfactor
    by_cases hR : R = 0
    · simp [hR]
    · simpa [Polynomial.natDegree_prod'] using hle hR
  rw [Finset.sum_image (fun i _ j _ hij => domain.injective hij)] at hsum
  exact False.elim <| hdeg.not_ge <| hsum.trans' <| by
    simpa [mul_comm] using Finset.sum_le_sum hroots

/-- Every explicit target decode supplies a linear factor of the specialized interpolant. -/
theorem targetDecode_dvd_specialized
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    {γ : IRSProfile.Field} (d : TargetDecode U γ) :
    Polynomial.X - Polynomial.C d.polynomial ∣ specializeZ I.polynomial γ := by
  classical
  apply Polynomial.dvd_iff_isRoot.mpr
  let R := (specializeZ I.polynomial γ).eval d.polynomial
  by_cases hR : R = 0
  · exact hR
  · exfalso
    have hPnat : d.polynomial.natDegree ≤ targetK - 1 := by
      have hp : d.polynomial.natDegree < targetK := by
        by_cases hz : d.polynomial = 0
        · simp [hz, targetK]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by
            simpa [targetK, IRSProfile.baseDimension] using d.degree_lt)
      omega
    have hdeg : R.natDegree < targetDX :=
      (natDegree_eval_le_weighted (specializeZ I.polynomial γ) d.polynomial
        targetK hPnat).trans_lt (specializeZ_weightedDegree_lt I γ)
    have hroots : ∀ i ∈ d.support,
        targetM ≤ R.rootMultiplicity (IRSProfile.domain i) := by
      intro i hi
      have horder : TargetHasOrderAt (specializeZ I.polynomial γ)
          (IRSProfile.domain i) (d.polynomial.eval (IRSProfile.domain i)) targetM := by
        intro r s hrs
        rw [d.agreement i hi, specializeZ_shift_coeff]
        rw [I.shift_vanishing i r s hrs]
        simp
      rcases orderAt_eval_ge_6317 (specializeZ I.polynomial γ) d.polynomial
          (IRSProfile.domain i) targetM horder with hz | hm
      · exact False.elim (hR hz)
      · exact hm
    have hcount : targetDX < targetM * d.support.card := by
      rw [d.support_card]
      norm_num [targetDX, targetM]
    have hz : R = 0 := eq_zero_of_many_multiplicity_roots IRSProfile.domain R
      targetM d.support hroots (hdeg.trans hcount)
    exact hR hz

end Specialization

end ProximityPrize.SubmissionLower
