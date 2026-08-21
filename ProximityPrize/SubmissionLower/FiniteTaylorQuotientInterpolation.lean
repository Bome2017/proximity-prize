import ProximityPrize.SubmissionLower.FiniteTaylorCore

/-!
# Coefficientwise quotient interpolation

This file isolates the algebraic step that turns `k+1` pointwise congruences
modulo a monic branch polynomial into one polynomial congruence in the Taylor
variable.  It deliberately does not import the finite-Taylor recursion.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorQuotientInterpolation

open scoped BigOperators
open Polynomial
open FiniteTaylorCore

noncomputable section

variable {F : Type*} [Field F]

/-- Reduce every coefficient in the outer polynomial variable modulo `H`.

The outer polynomial is over `F[Z][T]`; reduction is `F[Z]`-linear, hence it
commutes with evaluation of the outer variable at a constant from `F[Z]`.
-/
def coefficientwiseRemainder (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (Polynomial F)) :=
  PolynomialModule.equivPolynomial
    (PolynomialModule.map (Polynomial F) (Polynomial.modByMonicHom H)
      (PolynomialModule.equivPolynomial.symm D))

@[simp] theorem coeff_coefficientwiseRemainder
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F))) (i : Nat) :
    (coefficientwiseRemainder H D).coeff i =
      canonicalRemainder H (D.coeff i) := by
  rfl

theorem natDegree_coefficientwiseRemainder_le
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F))) :
    (coefficientwiseRemainder H D).natDegree ≤ D.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_coefficientwiseRemainder]
  have hDn : D.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [hDn, canonicalRemainder]

@[simp] theorem coefficientwiseRemainder_add
    (H : Polynomial (Polynomial F))
    (D E : Polynomial (Polynomial (Polynomial F))) :
    coefficientwiseRemainder H (D + E) =
      coefficientwiseRemainder H D + coefficientwiseRemainder H E := by
  apply Polynomial.ext
  intro i
  simp [canonicalRemainder, Polynomial.add_modByMonic]

@[simp] theorem coefficientwiseRemainder_monomial
    (H : Polynomial (Polynomial F)) (n : Nat)
    (a : Polynomial (Polynomial F)) :
    coefficientwiseRemainder H (Polynomial.monomial n a) =
      Polynomial.monomial n (canonicalRemainder H a) := by
  apply Polynomial.ext
  intro i
  by_cases hi : n = i
  · subst i
    simp
  · simp [Polynomial.coeff_monomial, hi, canonicalRemainder]

/-- Coefficientwise reduction commutes with evaluating the outer variable at
`C r`, because `%ₘ H` is linear over the coefficient ring `F[Z]`. -/
theorem eval_coefficientwiseRemainder_C
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F))) (r : Polynomial F) :
    (coefficientwiseRemainder H D).eval (Polynomial.C r) =
      canonicalRemainder H (D.eval (Polynomial.C r)) := by
  classical
  induction D using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, canonicalRemainder, Polynomial.add_modByMonic]
  | monomial n a =>
      simp only [coefficientwiseRemainder_monomial,
        Polynomial.eval_monomial, canonicalRemainder]
      change (a %ₘ H) * Polynomial.C r ^ n =
        (a * Polynomial.C r ^ n) %ₘ H
      rw [show Polynomial.C r ^ n = Polynomial.C (r ^ n) by simp]
      change (a %ₘ H) * Polynomial.C (r ^ n) =
        (a * Polynomial.C (r ^ n)) %ₘ H
      rw [mul_comm a, mul_comm (a %ₘ H)]
      simpa only [Polynomial.smul_eq_C_mul] using
        (Polynomial.smul_modByMonic (q := H) (r ^ n) a).symm

/-- Pointwise zero canonical remainders at sufficiently many distinct
constant points force the whole coefficientwise remainder polynomial to be
zero.  This is the honest quotient interpolation step; it uses no evaluation
injectivity at an algebraic root. -/
theorem coefficientwiseRemainder_eq_zero_of_many_evaluations
    {Index : Type*} [Fintype Index]
    (x : Index → F) (hx : Function.Injective x)
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F)))
    (hdegree : D.natDegree < Fintype.card Index)
    (hpoint : ∀ i,
      canonicalRemainder H (D.eval (Polynomial.C (Polynomial.C (x i)))) = 0) :
    coefficientwiseRemainder H D = 0 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (coefficientwiseRemainder H D) 0
    (f := fun i => Polynomial.C (Polynomial.C (x i)))
  · intro i j hij
    exact hx (Polynomial.C_injective (Polynomial.C_injective hij))
  · intro i
    rw [eval_coefficientwiseRemainder_C]
    simpa using hpoint i
  · simpa using (natDegree_coefficientwiseRemainder_le H D).trans_lt hdegree

/-- Once the coefficientwise remainder polynomial is zero, mapping every
coefficient to a specialized root of `H` kills the whole outer polynomial.
-/
theorem map_at_specialized_root_eq_zero_of_coefficientwiseRemainder_eq_zero
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F)))
    (hzero : coefficientwiseRemainder H D = 0)
    (z y : F) (hroot : (H.map (Polynomial.evalRingHom z)).eval y = 0) :
    D.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) = 0 := by
  have hcoeff : ∀ i, canonicalRemainder H (D.coeff i) = 0 := by
    intro i
    have := congrArg (fun P => P.coeff i) hzero
    simpa using this
  have hcoeffEval : ∀ i,
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) (D.coeff i) = 0 := by
    intro i
    have hdvdNeg : H ∣ -(D.coeff i) := by
      simpa [hcoeff i] using
        (canonicalRemainder_congruent (H := H) (D.coeff i))
    have hdvd : H ∣ D.coeff i := dvd_neg.mp hdvdNeg
    obtain ⟨K, hK⟩ := hdvd
    rw [hK, map_mul]
    change H.eval₂ (Polynomial.evalRingHom z) y *
      K.eval₂ (Polynomial.evalRingHom z) y = 0
    rw [Polynomial.eval₂_eq_eval_map, hroot, zero_mul]
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map]
  simp [hcoeffEval i]

/-- Scalar-evaluation form of
`map_at_specialized_root_eq_zero_of_coefficientwiseRemainder_eq_zero`. -/
theorem eval_at_specialized_root_of_coefficientwiseRemainder_eq_zero
    (H : Polynomial (Polynomial F))
    (D : Polynomial (Polynomial (Polynomial F)))
    (hzero : coefficientwiseRemainder H D = 0)
    (s z y : F) (hroot : (H.map (Polynomial.evalRingHom z)).eval y = 0) :
    (D.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)).eval s = 0 := by
  rw [map_at_specialized_root_eq_zero_of_coefficientwiseRemainder_eq_zero
    H D hzero z y hroot]
  simp

end

end ProximityPrize.SubmissionLower.FiniteTaylorQuotientInterpolation
