import ProximityPrize.SubmissionLower.FiniteTaylorCap72Height
import ProximityPrize.SubmissionLower.Target5314Extraction

/-!
# Concrete height and quotient-degree inputs for the Cap72 beta polynomials

Recentering changes only the outer interpolation variable, so scalar outer
evaluation has exactly the same coefficient height.  It also preserves the
strict degree bound in the quotient variable; subtracting the affine target,
which is constant in that variable, preserves the bound as well.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorBetaInputs

open Polynomial
open ProximityPrize.Benchmark
open FiniteTaylorCore FiniteTaylorExtraction
open Target5314Extraction

noncomputable section

variable {F : Type*} [Field F]

/-- Recentering the outer Taylor variable preserves the numerical Cap72
height bound after scalar outer evaluation. -/
theorem polyHeight_eval_unshiftTaylor_le_10104857200000
    (x₀ : F) (S : Polynomial (Polynomial (Polynomial F)))
    (hS : ∀ s : F,
      polyHeight (S.eval (Polynomial.C (Polynomial.C s))) ≤
        10104857200000) :
    ∀ s : F,
      polyHeight ((unshiftTaylor x₀ S).eval
        (Polynomial.C (Polynomial.C s))) ≤ 10104857200000 := by
  intro s
  unfold unshiftTaylor
  rw [Polynomial.eval_comp]
  convert hS (s - x₀) using 1 <;> simp

/-- Direct specialization of the preceding lemma to the common-denominator
Taylor truncation, with the height premise discharged by the Cap72 sequence
bound. -/
theorem polyHeight_eval_unshifted_commonDenominatorTaylorTruncation_le
    (x₀ : F) (h k : Nat) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F)
    (hk : k ≤ 131071) (hqdeg : q.natDegree ≤ 400000)
    (hseq : ∀ i ≤ k, vectorHeight (seq i) ≤ 10000000000000) :
    ∀ s : F,
      polyHeight
        ((unshiftTaylor x₀
          (commonDenominatorTaylorTruncation h k q seq)).eval
            (Polynomial.C (Polynomial.C s))) ≤ 10104857200000 := by
  apply polyHeight_eval_unshiftTaylor_le_10104857200000
  exact (commonDenominatorTaylorTruncation_height_lt_2pow47
    h k q seq hk hqdeg hseq).2.1

/-- Scalar outer evaluation of the common truncation remains in the quotient
basis `1,T,…,T^(h-1)`. -/
theorem commonDenominatorTaylorTruncation_eval_degree_lt
    (h k : Nat) (hh : 0 < h) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) (s : F) :
    ((commonDenominatorTaylorTruncation h k q seq).eval
      (Polynomial.C (Polynomial.C s))).degree < h := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  have hhn : h ≤ n := by exact_mod_cast hn
  unfold commonDenominatorTaylorTruncation
  rw [Polynomial.eval_finset_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.eval_monomial, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases hb : ab.2 = 0
  · have ha : h ≤ ab.1 := by
      have habsum : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
      omega
    rw [hb, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      Polynomial.eval_C]
    rw [Polynomial.coeff_C_mul,
      coeff_vectorPolynomial_eq_zero_of_le h (seq i) ab.1 ha]
    simp
  · have hconst : ((Polynomial.C (Polynomial.C s) :
        Polynomial (Polynomial F)) ^ i.1).coeff ab.2 = 0 := by
      rw [← map_pow]
      rw [Polynomial.coeff_C, if_neg hb]
    rw [hconst, mul_zero]

/-- Recentering the outer Taylor variable preserves strict quotient degree. -/
theorem unshiftTaylor_eval_degree_lt
    (x₀ s : F) (h k : Nat) (hh : 0 < h) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) :
    ((unshiftTaylor x₀
      (commonDenominatorTaylorTruncation h k q seq)).eval
        (Polynomial.C (Polynomial.C s))).degree < h := by
  unfold unshiftTaylor
  rw [Polynomial.eval_comp]
  convert commonDenominatorTaylorTruncation_eval_degree_lt
    h k hh q seq (s - x₀) using 1 <;> simp

/-- The beta numerator before canonical reduction still has degree `< h`:
the Taylor term has that bound, and the scaled affine row value is constant
in the quotient variable. -/
theorem unshifted_beta_predegree_lt
    (x₀ s : F) (h k : Nat) (hh : 0 < h) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F)
    (scale affine : Polynomial F) :
    ((unshiftTaylor x₀
      (commonDenominatorTaylorTruncation h k q seq)).eval
        (Polynomial.C (Polynomial.C s)) -
      Polynomial.C (scale * affine)).degree < h := by
  apply (Polynomial.degree_sub_le _ _).trans_lt
  apply max_lt
  · exact unshiftTaylor_eval_degree_lt x₀ s h k hh q seq
  · exact Polynomial.degree_C_le.trans_lt (by exact_mod_cast hh)

/-- Row-indexed form consumed directly by `canonical_beta_height_le`. -/
theorem unshifted_beta_predegree_rows_lt
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field) (h k : Nat) (hh : 0 < h)
    (q : Polynomial IRSProfile.Field)
    (seq : Nat → Fin h → Polynomial IRSProfile.Field)
    (scale : Polynomial IRSProfile.Field) (i : IRSProfile.Index) :
    ((unshiftTaylor x₀
      (commonDenominatorTaylorTruncation h k q seq)).eval
        (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
      Polynomial.C
        (scale * (Polynomial.C (rows 0 i) +
          Polynomial.X * Polynomial.C (rows 1 i)))).degree <
            (h : WithBot Nat) := by
  exact unshifted_beta_predegree_lt x₀ (IRSProfile.domain i) h k hh q seq
    scale (Polynomial.C (rows 0 i) +
      Polynomial.X * Polynomial.C (rows 1 i))

end

end ProximityPrize.SubmissionLower.FiniteTaylorBetaInputs
