/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Place6317

/-!
# Cleared value equations for a repaired Hensel branch

The paper informally evaluates the function-field Hensel coefficients at `Z = z`.  That is not
defined at poles.  This file instead clears every coefficient to the single denominator

`W^(k+1) * xi^e_k`

inside the regular quotient `O_H`.  At a good rational place the cleared equation specializes to
the expected value equation, while its weight telescopes to the corrected bound
`(2*k+1)*(deg_Y R+1)*D`.  This is the nonmonic replacement for the monic `aPre` calculation.
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal
open scoped BigOperators

namespace ProximityPrize.SubmissionLower.RF6317
noncomputable section CellAlgebra
namespace CellAlgebra

open HenselNumerators Place

variable {F : Type} [Field F]
variable {R : F[X][X][Y]} {H : F[X][Y]}
variable [hHirr : Fact (Irreducible H)] [hHpos : Fact (0 < H.natDegree)]

/-- A coefficient polynomial in `F[Z]`, regarded as an element of the regular quotient. -/
noncomputable def regularCoefficient (H : F[X][Y]) (p : F[X]) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C p)

@[simp] theorem embed_regularCoefficient (H : F[X][Y]) (p : F[X]) :
    embeddingOf𝒪Into𝑃 H (regularCoefficient H p) = liftToFunctionField (H := H) p := by
  simp [regularCoefficient, embeddingOf𝒪Into𝑃_mk, liftBivariate_C]

@[simp] theorem piZ_regularCoefficient (z : F) (root : rationalRoot (monicize H) z)
    (p : F[X]) :
    piZ z root (regularCoefficient H p) = p.eval z := by
  simp [regularCoefficient, piZ, piZLift]

/-- The regular element representing the affine function `a + Z*b`. -/
noncomputable def regularAffine (H : F[X][Y]) (a b : F) : 𝒪 H :=
  regularCoefficient H (Polynomial.C a + Polynomial.X * Polynomial.C b)

@[simp] theorem embed_regularAffine (H : F[X][Y]) (a b : F) :
    embeddingOf𝒪Into𝑃 H (regularAffine H a b) =
      liftToFunctionField (H := H)
        (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  simp [regularAffine]

@[simp] theorem piZ_regularAffine (z : F) (root : rationalRoot (monicize H) z)
    (a b : F) :
    piZ z root (regularAffine H a b) = a + z * b := by
  simp [regularAffine]

/-- The common-denominator version of the `t`-th Hensel value term. -/
noncomputable def clearedValueTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k t : ℕ) (e : F) : 𝒪 H :=
  betaSeq x₀ R H hHyp t *
    regularLeadingCoeff H ^ (k - t) *
    xi x₀ R H hHyp ^
      (henselDenominatorExponent k - henselDenominatorExponent t) *
    regularCoefficient H (Polynomial.C (e ^ t))

/-- The numerator of
`sum_(t<k) alpha_t e^t - (a + Z*b)` after clearing the common denominator. -/
noncomputable def clearedValue (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k : ℕ) (e a b : F) : 𝒪 H :=
  (∑ t ∈ Finset.range k, clearedValueTerm x₀ R H hHyp k t e) -
    regularAffine H a b * regularLeadingCoeff H ^ (k + 1) *
      xi x₀ R H hHyp ^ henselDenominatorExponent k

lemma henselDenominatorExponent_mono {s t : ℕ} (hst : s ≤ t) :
    henselDenominatorExponent s ≤ henselDenominatorExponent t := by
  unfold henselDenominatorExponent
  split_ifs with hs ht <;> omega

/-- Embedding a cleared term recovers the common denominator times `alpha_t*e^t`. -/
theorem embed_clearedValueTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k t : ℕ) (ht : t < k) (e : F)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0)
    (hxi : embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ≠ 0) :
    embeddingOf𝒪Into𝑃 H (clearedValueTerm x₀ R H hHyp k t e) =
      (liftToFunctionField (H := H) H.leadingCoeff ^ (k + 1) *
        embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ^
          henselDenominatorExponent k) *
        (alpha x₀ R H hHyp t * fieldTo𝑃 (H := H) (e ^ t)) := by
  have htk : t + 1 ≤ k := by omega
  have hEk := henselDenominatorExponent_mono (s := t) (t := k) (Nat.le_of_lt ht)
  simp only [clearedValueTerm, map_mul, map_pow, embed_regularLeadingCoeff,
    embed_regularCoefficient, alpha, alphaOfNumerators, fieldTo𝑃]
  rw [show k - t + (t + 1) = k + 1 by omega,
    show henselDenominatorExponent k - henselDenominatorExponent t +
        henselDenominatorExponent t = henselDenominatorExponent k by omega]
  field_simp [hW, hxi]
  ring

/-- The embedded cleared value is the common denominator times the desired value difference. -/
theorem embed_clearedValue (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k : ℕ) (e a b : F)
    (hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0)
    (hxi : embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ≠ 0) :
    embeddingOf𝒪Into𝑃 H (clearedValue x₀ R H hHyp k e a b) =
      (liftToFunctionField (H := H) H.leadingCoeff ^ (k + 1) *
        embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ^
          henselDenominatorExponent k) *
        ((∑ t ∈ Finset.range k,
          alpha x₀ R H hHyp t * fieldTo𝑃 (H := H) (e ^ t)) -
          liftToFunctionField (H := H)
            (Polynomial.C a + Polynomial.X * Polynomial.C b)) := by
  classical
  simp only [clearedValue, map_sub, map_mul, map_pow, embed_regularAffine,
    embed_regularLeadingCoeff, map_sum]
  rw [Finset.sum_congr rfl fun t ht => embed_clearedValueTerm x₀ R H hHyp k t
    (Finset.mem_range.mp ht) e hW hxi]
  rw [Finset.mul_sum]
  ring

/-- Specialization of a cleared term at a good rational place. -/
theorem piZ_clearedValueTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k t : ℕ) (ht : t < k) (e z : F)
    (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) :
    piZ z root (clearedValueTerm x₀ R H hHyp k t e) =
      (H.leadingCoeff.eval z ^ (k + 1) *
        piZ z root (xi x₀ R H hHyp) ^ henselDenominatorExponent k) *
        (alphaAt x₀ R H hHyp z root hW hxi t * e ^ t) := by
  have hEk := henselDenominatorExponent_mono (s := t) (t := k) (Nat.le_of_lt ht)
  simp only [clearedValueTerm, map_mul, map_pow, piZ_regularLeadingCoeff,
    piZ_regularCoefficient, Polynomial.eval_C, alphaAt]
  rw [show k - t + (t + 1) = k + 1 by omega,
    show henselDenominatorExponent k - henselDenominatorExponent t +
        henselDenominatorExponent t = henselDenominatorExponent k by omega]
  field_simp [hW, hxi]
  ring

/-- A decoded value equation makes the cleared numerator vanish at the place. -/
theorem piZ_clearedValue_eq_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k : ℕ) (e a b z : F)
    (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0)
    (hvalue : ∑ t ∈ Finset.range k,
      alphaAt x₀ R H hHyp z root hW hxi t * e ^ t = a + z * b) :
    piZ z root (clearedValue x₀ R H hHyp k e a b) = 0 := by
  classical
  simp only [clearedValue, map_sub, map_mul, map_pow, piZ_regularAffine,
    piZ_regularLeadingCoeff, map_sum]
  rw [Finset.sum_congr rfl fun t ht => piZ_clearedValueTerm x₀ R H hHyp k t
    (Finset.mem_range.mp ht) e z root hW hxi]
  rw [Finset.mul_sum, hvalue]
  ring

/-- The `xi` budget including the content correction missing from the paper. -/
def xiBudget (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) (D : ℕ) : ℕ :=
  (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) +
    contentWeight x₀ R H

lemma numeratorShapeSharp_telescope (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (D : ℕ) {t k : ℕ} (ht : t ≤ k) :
    numeratorShapeSharp x₀ R H D t +
        (k - t) * (D - Bivariate.natDegreeY H) +
        (henselDenominatorExponent k - henselDenominatorExponent t) *
          xiBudget x₀ R H D ≤
      numeratorShapeSharp x₀ R H D k := by
  have hE := henselDenominatorExponent_mono (s := t) (t := k) ht
  have hk : t + (k - t) = k := Nat.add_sub_of_le ht
  have he : henselDenominatorExponent t +
      (henselDenominatorExponent k - henselDenominatorExponent t) =
        henselDenominatorExponent k := Nat.add_sub_of_le hE
  unfold numeratorShapeSharp xiBudget
  have hcorr : (t - 1) * (D - Bivariate.natDegreeY R) ≤
      (k - 1) * (D - Bivariate.natDegreeY R) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ht 1)
  rw [← hk, ← he]
  ring_nf at ⊢
  exact hcorr

/-- `a + Z*b` has regular weight at most one. -/
theorem regularAffine_weight_le (hH : 0 < H.natDegree) {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (a b : F) :
    regularWeight hH (regularAffine H a b) D ≤ (WithBot.some 1 : WithBot ℕ) := by
  apply regularWeight_le_of_regularWeightLe
  rw [embed_regularAffine]
  refine (regularWeightLe_liftToFunctionField hD hH
    (Polynomial.C a + Polynomial.X * Polynomial.C b)).mono ?_
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp

/-- The common cleared value has the corrected generic weight bound. -/
theorem clearedValue_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.degreeX (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (k : ℕ) (e a b : F) :
    regularWeight hH (clearedValue x₀ R H hHyp k e a b) D ≤
      (WithBot.some ((2 * k + 1) * (Bivariate.natDegreeY R + 1) * D) : WithBot ℕ) := by
  classical
  let W : 𝒪 H := regularLeadingCoeff H
  let eta : 𝒪 H := xi x₀ R H hHyp
  let L := (2 * k + 1) * (Bivariate.natDegreeY R + 1) * D
  have hD_Rx0 := evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
  have hWw : regularWeight hH W D ≤
      (WithBot.some (D - Bivariate.natDegreeY H) : WithBot ℕ) := by
    apply regularWeight_le_of_regularWeightLe
    simpa [W, Bivariate.natDegreeY] using regularWeightLe_leadingCoeff_sharp hD_H hH
  have hetaw : regularWeight hH eta D ≤
      (WithBot.some (xiBudget x₀ R H D) : WithBot ℕ) := by
    unfold eta xiBudget
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hbeta (t : ℕ) : regularWeight hH (betaSeq x₀ R H hHyp t) D ≤
      (WithBot.some (numeratorShapeSharp x₀ R H D t) : WithBot ℕ) :=
    hensel_numerator_weight_sharp_le x₀ R H hHyp hH hD_H hD_R hRdeg
      (betaSeq_spec x₀ R H hHyp) t
  have hconst (c : F) : regularWeight hH
      (regularCoefficient H (Polynomial.C c)) D ≤ (WithBot.some 0 : WithBot ℕ) := by
    apply regularWeight_le_of_regularWeightLe
    rw [embed_regularCoefficient]
    exact (regularWeightLe_liftToFunctionField hD_H hH (Polynomial.C c)).mono (by simp)
  have hterm (t : ℕ) (ht : t ∈ Finset.range k) :
      regularWeight hH (clearedValueTerm x₀ R H hHyp k t e) D ≤
        (WithBot.some L : WithBot ℕ) := by
    have htk : t ≤ k := (Finset.mem_range.mp ht).le
    have h1 := regularWeight_mul_le' hD_H hH (hbeta t)
      (regularWeight_mul_le' hD_H hH
        (show regularWeight hH (W ^ (k - t)) D ≤
          (WithBot.some ((k - t) * (D - Bivariate.natDegreeY H)) : WithBot ℕ) by
          apply regularWeight_le_of_regularWeightLe
          exact (RegularWeightLe.pow hD_H
            (show RegularWeightLe hH (embeddingOf𝒪Into𝑃 H W) D
              (D - Bivariate.natDegreeY H) by
              exact ⟨W, rfl, hWw⟩) (k - t)).mono (by ring))
        (show regularWeight hH (eta ^
            (henselDenominatorExponent k - henselDenominatorExponent t)) D ≤
          (WithBot.some ((henselDenominatorExponent k - henselDenominatorExponent t) *
            xiBudget x₀ R H D) : WithBot ℕ) by
          apply regularWeight_le_of_regularWeightLe
          exact RegularWeightLe.pow hD_H
            (show RegularWeightLe hH (embeddingOf𝒪Into𝑃 H eta) D
              (xiBudget x₀ R H D) by exact ⟨eta, rfl, hetaw⟩) _))
    have h2 := regularWeight_mul_le' hD_H hH h1 (hconst (e ^ t))
    refine h2.trans ?_
    rw [WithBot.coe_le_coe]
    refine (Nat.add_le_add_right
      (numeratorShapeSharp_telescope x₀ R H D htk) 0).trans ?_
    exact numeratorShapeSharp_le_loose x₀ R H hHyp hH
      (by simpa [Bivariate.natDegreeY] using hRdeg) hD_H hD_Rx0 k
  have hsum : regularWeight hH
      (∑ t ∈ Finset.range k, clearedValueTerm x₀ R H hHyp k t e) D ≤
        (WithBot.some L : WithBot ℕ) := by
    induction Finset.range k using Finset.induction_on with
    | empty => simp [regularWeight_zero]
    | @insert t s ht ih =>
        rw [Finset.sum_insert ht]
        exact (regularWeight_add_le hD_H hH _ _).trans
          (max_le (hterm t (by simp)) (ih (fun u hu => hterm u (by simp [hu]))))
  have hground : regularWeight hH
      (regularAffine H a b * W ^ (k + 1) * eta ^ henselDenominatorExponent k) D ≤
        (WithBot.some L : WithBot ℕ) := by
    have h1 := regularWeight_mul_le' hD_H hH (regularAffine_weight_le hH hD_H a b)
      (show regularWeight hH (W ^ (k + 1)) D ≤
        (WithBot.some ((k + 1) * (D - Bivariate.natDegreeY H)) : WithBot ℕ) by
        apply regularWeight_le_of_regularWeightLe
        exact RegularWeightLe.pow hD_H
          (show RegularWeightLe hH (embeddingOf𝒪Into𝑃 H W) D
            (D - Bivariate.natDegreeY H) by exact ⟨W, rfl, hWw⟩) _)
    have h2 := regularWeight_mul_le' hD_H hH h1
      (show regularWeight hH (eta ^ henselDenominatorExponent k) D ≤
        (WithBot.some (henselDenominatorExponent k * xiBudget x₀ R H D) : WithBot ℕ) by
        apply regularWeight_le_of_regularWeightLe
        exact RegularWeightLe.pow hD_H
          (show RegularWeightLe hH (embeddingOf𝒪Into𝑃 H eta) D
            (xiBudget x₀ R H D) by exact ⟨eta, rfl, hetaw⟩) _)
    refine h2.trans ?_
    rw [WithBot.coe_le_coe]
    refine (show 1 + (k + 1) * (D - Bivariate.natDegreeY H) +
        henselDenominatorExponent k * xiBudget x₀ R H D ≤
          numeratorShapeSharp x₀ R H D k by
      unfold numeratorShapeSharp xiBudget
      omega).trans ?_
    exact numeratorShapeSharp_le_loose x₀ R H hHyp hH
      (by simpa [Bivariate.natDegreeY] using hRdeg) hD_H hD_Rx0 k
  unfold clearedValue
  exact (regularWeight_add_le hD_H hH _ _).trans
    (max_le hsum (by simpa [regularWeight_neg] using hground))

end CellAlgebra
end CellAlgebra
end ProximityPrize.SubmissionLower.RF6317
