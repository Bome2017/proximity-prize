import ProximityPrize.SubmissionLower.Cap72Interpolation

namespace ProximityPrize.SubmissionLower.Cap72

open Polynomial
open ProximityPrize.Benchmark

set_option maxRecDepth 1000000

/-- Every nested `(Y,X)` coefficient of the capped interpolant has `Z`-degree at most 72. -/
theorem coeff_toPolynomial_natDegree_le_seventyTwo
    {F : Type*} [Field F] (v : MonomialIndex → F) (y x : ℕ) :
    (((toPolynomial v).coeff y).coeff x).natDegree ≤ 72 := by
  classical
  unfold toPolynomial
  simp only [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  simp only [monomial]
  by_cases hy : yDegree q = y
  · rw [Polynomial.coeff_monomial, if_pos hy]
    by_cases hx : xDegree q = x
    · rw [Polynomial.coeff_monomial, if_pos hx]
      apply (Polynomial.natDegree_monomial_le (v q)).trans
      exact (Nat.le_add_right (zDegree q) (yDegree q)).trans (zDegree_add_yDegree_le q)
    · rw [Polynomial.coeff_monomial, if_neg hx, Polynomial.natDegree_zero]
      norm_num
  · rw [Polynomial.coeff_monomial, if_neg hy, Polynomial.coeff_zero,
      Polynomial.natDegree_zero]
    norm_num

/-- A nonzero capped interpolant exposes a nonzero nested coefficient whose `Z`-degree
is at most 72, exactly the witness needed by the content-root discard. -/
theorem Interpolant.exists_nonzero_coeff_degree_le_seventyTwo
    {F : Type*} [Field F] {domain : IRSProfile.Index → F}
    {u v : IRSProfile.Index → F} (Q : Interpolant domain u v) :
    ∃ y x : ℕ,
      (Q.polynomial.coeff y).coeff x ≠ 0 ∧
      ((Q.polynomial.coeff y).coeff x).natDegree ≤ 72 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, Q.coefficients q ≠ 0 := by
    by_contra h
    push Not at h
    apply Q.coefficients_ne_zero
    funext q
    exact h q
  refine ⟨yDegree q, xDegree q, ?_,
    coeff_toPolynomial_natDegree_le_seventyTwo Q.coefficients _ _⟩
  intro hzero
  change (((toPolynomial Q.coefficients).coeff (yDegree q)).coeff (xDegree q)) = 0 at hzero
  have hcoeff := coeff_toPolynomial Q.coefficients q
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact hq hcoeff.symm

end ProximityPrize.SubmissionLower.Cap72
