import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale

open Polynomial

noncomputable section

/-- Division-free homogenizing scale in the outer variable.  When `d` bounds
the degree of `P`, this represents `W^d P(T/W)` without introducing `W⁻¹`. -/
def integralScaleAt {R : Type*} [CommRing R] (d : ℕ) (W : R)
    (P : Polynomial R) : Polynomial R :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i (P.coeff i * W ^ (d - i))

@[simp] theorem integralScaleAt_coeff_of_le
    {R : Type*} [CommRing R] (d : ℕ) (W : R) (P : Polynomial R)
    (i : ℕ) (hi : i ≤ d) :
    (integralScaleAt d W P).coeff i = P.coeff i * W ^ (d - i) := by
  classical
  unfold integralScaleAt
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [hbi]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem integralScaleAt_eq_scaleRoots
    {R : Type*} [CommRing R] (d : ℕ) (W : R) (P : Polynomial R)
    (hdegree : P.natDegree = d) :
    integralScaleAt d W P = P.scaleRoots W := by
  ext i
  by_cases hi : i ≤ d
  · rw [integralScaleAt_coeff_of_le d W P i hi,
      Polynomial.coeff_scaleRoots, hdegree]
  · have hcoeff : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_scaleRoots, hcoeff, zero_mul]
    classical
    unfold integralScaleAt
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro b hb
    simp only [ite_eq_right_iff]
    intro hbi
    subst b
    exact (hi (by simpa using Finset.mem_range.mp hb)).elim

theorem derivative_scaleRoots_eq_scaleRoots_derivative
    {F : Type*} [Field F] (W : F) (P : Polynomial F)
    (hderivative : P.derivative.natDegree = P.natDegree - 1) :
    (P.scaleRoots W).derivative = P.derivative.scaleRoots W := by
  ext i
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots,
    hderivative]
  have hexp : P.natDegree - (i + 1) = P.natDegree - 1 - i := by omega
  rw [hexp]
  ring

/-- A nonzero scaling of the roots preserves separability.  The derivative
degree hypothesis is explicit because it is exactly where characteristic can
matter. -/
theorem scaleRoots_separable
    {F : Type*} [Field F] (W : F) (P : Polynomial F)
    (hW : W ≠ 0) (hsep : P.Separable)
    (hderivative : P.derivative.natDegree = P.natDegree - 1) :
    (P.scaleRoots W).Separable := by
  have hres : Polynomial.resultant P P.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero P P.derivative hsep
  have hscaledRes : Polynomial.resultant (P.scaleRoots W)
      (P.derivative.scaleRoots W) ≠ 0 := by
    rw [Polynomial.resultant_scaleRoots]
    exact mul_ne_zero (pow_ne_zero _ hW) hres
  have hcoprime : IsCoprime (P.scaleRoots W)
      (P.derivative.scaleRoots W) := by
    by_contra hnot
    apply hscaledRes
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl (Polynomial.scaleRoots_ne_zero hsep.ne_zero W), hnot⟩
  rw [Polynomial.separable_def,
    derivative_scaleRoots_eq_scaleRoots_derivative W P hderivative]
  exact hcoprime

theorem isUnit_of_scaleRoots_isUnit
    {F : Type*} [Field F] (W : F) (P : Polynomial F)
    (hunit : IsUnit (P.scaleRoots W)) : IsUnit P := by
  have hP0 : P ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.zero_scaleRoots] at hunit
    exact not_isUnit_zero hunit
  have hdeg : P.natDegree = 0 := by
    rw [← Polynomial.natDegree_scaleRoots P W]
    exact Polynomial.natDegree_eq_zero_of_isUnit hunit
  have hconst : Polynomial.C (P.coeff 0) = P :=
    (Polynomial.eq_C_of_natDegree_eq_zero hdeg).symm
  rw [← hconst] at hP0 ⊢
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (fun h => hP0 (by simpa [h])))

/-- Multiplying all roots by a nonzero field element preserves
irreducibility. -/
theorem irreducible_scaleRoots
    {F : Type*} [Field F] (W : F) (P : Polynomial F)
    (hW : W ≠ 0) (hirr : Irreducible P) :
    Irreducible (P.scaleRoots W) := by
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hirr.not_isUnit (isUnit_of_scaleRoots_isUnit W P hunit)
  · intro a b hab
    have hback := congrArg (fun Q : Polynomial F => Q.scaleRoots W⁻¹) hab
    have hWinv : W * W⁻¹ = 1 := mul_inv_cancel₀ hW
    rw [Polynomial.mul_scaleRoots_of_noZeroDivisors,
      ← Polynomial.scaleRoots_mul, hWinv, Polynomial.scaleRoots_one] at hback
    rcases hirr.isUnit_or_isUnit hback with ha | hb
    · exact Or.inl (isUnit_of_scaleRoots_isUnit W⁻¹ a ha)
    · exact Or.inr (isUnit_of_scaleRoots_isUnit W⁻¹ b hb)

theorem integralScaleAt_derivative_eval
    {F : Type*} [Field F] (d : ℕ) (W y : F) (P : Polynomial F)
    (hpos : 0 < d) (hdegree : P.natDegree ≤ d) :
    (integralScaleAt d W P).derivative.eval (W * y) =
      W ^ (d - 1) * P.derivative.eval y := by
  classical
  have hPsum : P = ∑ i ∈ Finset.range (d + 1),
      Polynomial.monomial i (P.coeff i) := by
    exact Polynomial.as_sum_range' P (d + 1) (by omega)
  rw [integralScaleAt, map_sum, Polynomial.eval_finset_sum]
  calc
    ∑ i ∈ Finset.range (d + 1),
        (Polynomial.monomial i (P.coeff i * W ^ (d - i))).derivative.eval
          (W * y) =
      ∑ i ∈ Finset.range (d + 1), W ^ (d - 1) *
        (Polynomial.monomial i (P.coeff i)).derivative.eval y := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases i with _ | i
          · rw [Polynomial.monomial_zero_left, Polynomial.derivative_C,
              Polynomial.eval_zero]
            simp
          · have hid : i + 1 ≤ d := by
              simpa [Finset.mem_range] using hi
            have hexp : d - (i + 1) + i = d - 1 := by omega
            simp only [Polynomial.derivative_monomial,
              Polynomial.eval_monomial, Nat.succ_sub_one]
            rw [mul_pow]
            calc
              P.coeff (i + 1) * W ^ (d - (i + 1)) * ((i + 1 : ℕ) : F) *
                    (W ^ i * y ^ i) =
                  (W ^ (d - (i + 1)) * W ^ i) *
                    (P.coeff (i + 1) * ((i + 1 : ℕ) : F) * y ^ i) := by ring
              _ = W ^ (d - 1) *
                    (P.coeff (i + 1) * ((i + 1 : ℕ) : F) * y ^ i) := by
                    rw [← pow_add, hexp]
    _ = W ^ (d - 1) *
        (∑ i ∈ Finset.range (d + 1),
          (Polynomial.monomial i (P.coeff i)).derivative.eval y) := by
            rw [Finset.mul_sum]
    _ = W ^ (d - 1) * P.derivative.eval y := by
          rw [← Polynomial.eval_finset_sum, ← map_sum, ← hPsum]

theorem integralScaleAt_derivative_eval_ne_zero
    {F : Type*} [Field F] (d : ℕ) (W y : F) (P : Polynomial F)
    (hpos : 0 < d) (hdegree : P.natDegree ≤ d)
    (hW : W ≠ 0) (hderiv : P.derivative.eval y ≠ 0) :
    (integralScaleAt d W P).derivative.eval (W * y) ≠ 0 := by
  rw [integralScaleAt_derivative_eval d W y P hpos hdegree]
  exact mul_ne_zero (pow_ne_zero _ hW) hderiv

end

end ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale
