/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.HenselSequence6317

/-!
# Hensel uniqueness for polynomials with power-series coefficients

This is the local, coefficientwise uniqueness theorem needed when a function-field Hensel lift is
specialized at a rational place.  It deliberately does not assume that the polynomial is monic:
a unit derivative at the common constant term is the exact hypothesis used by the application.
-/

namespace ProximityPrize.SubmissionLower.Series6317

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Agreement below an order propagates through every power. -/
theorem coeff_pow_sub_below {gamma₁ gamma₂ : R⟦X⟧} {t : ℕ}
    (h : ∀ j < t, coeff j gamma₁ = coeff j gamma₂) :
    ∀ i j, j < t → coeff j (gamma₁ ^ i) = coeff j (gamma₂ ^ i) := by
  intro i
  induction i with
  | zero => intro j _; simp
  | succ i ih =>
      intro j hj
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      have h1 : p.1 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_right _ _) hj
      have h2 : p.2 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_left _ _) hj
      rw [ih p.1 h1, h p.2 h2]

/-- The order-`t` response of a power to changing its order-`t` coefficient. -/
theorem coeff_pow_sub_at {gamma₁ gamma₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j gamma₁ = coeff j gamma₂) :
    ∀ i, coeff t (gamma₁ ^ (i + 1)) - coeff t (gamma₂ ^ (i + 1)) =
      (i + 1) • ((constantCoeff gamma₁) ^ i * (coeff t gamma₁ - coeff t gamma₂)) := by
  set c := constantCoeff gamma₁ with hc
  have hc2 : constantCoeff gamma₂ = c := by
    rw [hc, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (h 0 ht).symm
  intro i
  induction i with
  | zero => simp only [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | succ i ih =>
      have hA : ∀ j < t, coeff j (gamma₁ ^ (i + 1)) = coeff j (gamma₂ ^ (i + 1)) :=
        coeff_pow_sub_below h (i + 1)
      rw [pow_succ gamma₁ (i + 1), pow_succ gamma₂ (i + 1), coeff_mul, coeff_mul,
        ← Finset.sum_sub_distrib]
      have ht0 : (t, 0) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have h0t : (0, t) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      have hne : ((t, 0) : ℕ × ℕ) ≠ (0, t) :=
        fun hcontra => ht.ne' (Prod.ext_iff.mp hcontra).1
      rw [Finset.sum_eq_add_of_mem (t, 0) (0, t) ht0 h0t hne ?_]
      · have e0₁ : coeff (0, t).1 (gamma₁ ^ (i + 1)) = c ^ (i + 1) := by
          simp only [coeff_zero_eq_constantCoeff_apply, map_pow, ← hc]
        have e0₂ : coeff (0, t).1 (gamma₂ ^ (i + 1)) = c ^ (i + 1) := by
          simp only [coeff_zero_eq_constantCoeff_apply, map_pow, hc2]
        have ec₁ : coeff (t, 0).2 gamma₁ = c := by
          simp only [coeff_zero_eq_constantCoeff_apply, ← hc]
        have ec₂ : coeff (t, 0).2 gamma₂ = c := by
          simp only [coeff_zero_eq_constantCoeff_apply, hc2]
        change (coeff (t, 0).1 (gamma₁ ^ (i + 1)) * coeff (t, 0).2 gamma₁
                - coeff (t, 0).1 (gamma₂ ^ (i + 1)) * coeff (t, 0).2 gamma₂)
              + (coeff (0, t).1 (gamma₁ ^ (i + 1)) * coeff (0, t).2 gamma₁
                - coeff (0, t).1 (gamma₂ ^ (i + 1)) * coeff (0, t).2 gamma₂)
            = (i + 1 + 1) • (c ^ (i + 1) * (coeff t gamma₁ - coeff t gamma₂))
        rw [ec₁, ec₂, e0₁, e0₂]
        change (coeff t (gamma₁ ^ (i + 1)) * c - coeff t (gamma₂ ^ (i + 1)) * c)
              + (c ^ (i + 1) * coeff t gamma₁ - c ^ (i + 1) * coeff t gamma₂)
            = (i + 1 + 1) • (c ^ (i + 1) * (coeff t gamma₁ - coeff t gamma₂))
        rw [← sub_mul, ih]
        simp only [nsmul_eq_mul, pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      · intro p hp hp'
        rw [Finset.mem_antidiagonal] at hp
        obtain ⟨hpt0, hp0t⟩ := hp'
        have hb_lt : p.2 < t := by
          rcases lt_or_eq_of_le (show p.2 ≤ t from by rw [← hp]; exact Nat.le_add_left _ _)
            with hlt | heq
          · exact hlt
          · exact absurd
              (Prod.ext (show p.1 = (0, t).1 by simp; omega) (by simpa using heq)) hp0t
        have ha_lt : p.1 < t := by
          rcases lt_or_eq_of_le (show p.1 ≤ t from by rw [← hp]; exact Nat.le_add_right _ _)
            with hlt | heq
          · exact hlt
          · exact absurd
              (Prod.ext (by simpa using heq) (show p.2 = (t, 0).2 by simp; omega)) hpt0
        rw [hA p.1 ha_lt, h p.2 hb_lt, sub_self]

/-- Reduce the coefficients of a series-coefficient polynomial modulo the series variable. -/
noncomputable def constantPolynomial (Q : Polynomial R⟦X⟧) : Polynomial R :=
  Q.map (constantCoeff (R := R))

@[simp] theorem coeff_constantPolynomial (Q : Polynomial R⟦X⟧) (i : ℕ) :
    (constantPolynomial Q).coeff i = constantCoeff (Q.coeff i) := by
  rw [constantPolynomial, Polynomial.coeff_map]

theorem natDegree_constantPolynomial_le (Q : Polynomial R⟦X⟧) :
    (constantPolynomial Q).natDegree ≤ Q.natDegree :=
  Polynomial.natDegree_map_le

theorem coeff_eval_eq_sum_range (Q : Polynomial R⟦X⟧) (gamma : R⟦X⟧) (t : ℕ) :
    coeff t (Polynomial.eval gamma Q) =
      ∑ i ∈ Finset.range (Q.natDegree + 1), coeff t (Q.coeff i * gamma ^ i) := by
  rw [Polynomial.eval_eq_sum_range, map_sum]

/-- The coefficientwise Newton linearization for series-coefficient polynomials. -/
theorem coeff_eval_sub_at (Q : Polynomial R⟦X⟧) {gamma₁ gamma₂ : R⟦X⟧} {t : ℕ}
    (ht : 0 < t) (h : ∀ j < t, coeff j gamma₁ = coeff j gamma₂) :
    coeff t (Polynomial.eval gamma₁ Q) - coeff t (Polynomial.eval gamma₂ Q) =
      Polynomial.eval (constantCoeff gamma₁) (Polynomial.derivative (constantPolynomial Q)) *
        (coeff t gamma₁ - coeff t gamma₂) := by
  set c := constantCoeff gamma₁ with hc
  set delta := coeff t gamma₁ - coeff t gamma₂ with hdelta
  rw [coeff_eval_eq_sum_range, coeff_eval_eq_sum_range, ← Finset.sum_sub_distrib]
  have hstep : ∀ i ∈ Finset.range (Q.natDegree + 1),
      coeff t (Q.coeff i * gamma₁ ^ i) - coeff t (Q.coeff i * gamma₂ ^ i) =
        constantCoeff (Q.coeff i) * i * c ^ (i - 1) * delta := by
    intro i _
    have hcorner :
        coeff t (Q.coeff i * gamma₁ ^ i) - coeff t (Q.coeff i * gamma₂ ^ i) =
          constantCoeff (Q.coeff i) * (coeff t (gamma₁ ^ i) - coeff t (gamma₂ ^ i)) := by
      rw [coeff_mul, coeff_mul, ← Finset.sum_sub_distrib]
      have h0t : (0, t) ∈ Finset.antidiagonal t := by simp [Finset.mem_antidiagonal]
      rw [Finset.sum_eq_single_of_mem (0, t) h0t ?_]
      · simp only [coeff_zero_eq_constantCoeff_apply, mul_sub]
      · intro p hp hpne
        rw [Finset.mem_antidiagonal] at hp
        have hb_lt : p.2 < t := by
          rcases lt_or_eq_of_le (show p.2 ≤ t from by rw [← hp]; exact Nat.le_add_left _ _)
            with hlt | heq
          · exact hlt
          · exact absurd
              (Prod.ext (show p.1 = (0, t).1 by simp; omega) (by simpa using heq)) hpne
        rw [coeff_pow_sub_below h i p.2 hb_lt, sub_self]
    rw [hcorner]
    rcases i with _ | i
    · simp only [pow_zero, coeff_one, Nat.cast_zero, mul_zero, zero_mul]
      rw [if_neg (by omega), sub_zero, mul_zero]
    · rw [coeff_pow_sub_at ht h i, ← hc, ← hdelta, Nat.add_sub_cancel, nsmul_eq_mul]
      push_cast
      ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  congr 1
  rw [Polynomial.derivative_eval]
  have hQQ : ∀ i, constantCoeff (Q.coeff i) = (constantPolynomial Q).coeff i :=
    fun i => (coeff_constantPolynomial Q i).symm
  simp only [hQQ]
  rw [Polynomial.sum_over_range' _ (by simp) (Q.natDegree + 1)
        (Nat.lt_succ_of_le (natDegree_constantPolynomial_le Q))]

/-- Two roots with the same simple constant term are equal. -/
theorem root_unique {Q : Polynomial R⟦X⟧} {gamma₁ gamma₂ : R⟦X⟧}
    (hcc : constantCoeff gamma₁ = constantCoeff gamma₂)
    (hu : IsUnit
      (Polynomial.eval (constantCoeff gamma₁) (Polynomial.derivative (constantPolynomial Q))))
    (h₁ : Polynomial.eval gamma₁ Q = 0) (h₂ : Polynomial.eval gamma₂ Q = 0) :
    gamma₁ = gamma₂ := by
  by_contra hne
  have hex : ∃ t, coeff t gamma₁ ≠ coeff t gamma₂ := by
    by_contra hall
    push Not at hall
    exact hne (PowerSeries.ext fun t => hall t)
  classical
  let t := Nat.find hex
  have ht_ne : coeff t gamma₁ ≠ coeff t gamma₂ := Nat.find_spec hex
  have hbelow : ∀ j < t, coeff j gamma₁ = coeff j gamma₂ := fun j hj => by
    by_contra hjne
    exact absurd (Nat.find_le hjne) (not_le.mpr hj)
  have ht_pos : 0 < t := by
    refine Nat.pos_of_ne_zero fun ht0 => ht_ne ?_
    rw [ht0, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hcc]
  have hlin := coeff_eval_sub_at Q (gamma₁ := gamma₁) (gamma₂ := gamma₂) ht_pos hbelow
  rw [h₁, h₂] at hlin
  simp only [map_zero, sub_self] at hlin
  set A := Polynomial.eval (constantCoeff gamma₁)
    (Polynomial.derivative (constantPolynomial Q)) with hA
  have hAu : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hu
  have hzero : coeff t gamma₁ - coeff t gamma₂ = 0 := by
    have hmul := congrArg (fun x => Ring.inverse A * x) hlin
    simp only [mul_zero, ← mul_assoc, hAu, one_mul] at hmul
    exact hmul.symm
  exact ht_ne (sub_eq_zero.mp hzero)

end ProximityPrize.SubmissionLower.Series6317
