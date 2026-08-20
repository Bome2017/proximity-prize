/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.SeriesUniqueness6317

/-!
# Specializing the repaired nonmonic Hensel lift at a rational place

The function field itself cannot be evaluated at `Z = z`: a rational function may have a pole at
`z`.  The coefficients used by the Hensel construction have only the two explicit denominators
`W = lc_Y(H)` and `xi`.  We therefore work in the localization of the regular ring away from
`W * xi`.  It embeds into the function field, and at a place where both factors are nonzero it
also maps to the ground field.  Transporting the root identity through these two maps gives the
coefficient-reading statement without any hidden monicity assumption.
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace ProximityPrize.SubmissionLower.RF6317
noncomputable section PlaceSpecialization
namespace Place

open HenselNumerators

variable {F : Type} [Field F]
variable {R : F[X][X][Y]} {H : F[X][Y]}
variable [hHirr : Fact (Irreducible H)] [hHpos : Fact (0 < H.natDegree)]

/-- The leading coefficient, as an element of the regular quotient. -/
noncomputable def regularLeadingCoeff (H : F[X][Y]) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C H.leadingCoeff)

@[simp] theorem embed_regularLeadingCoeff (H : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (regularLeadingCoeff H) =
      liftToFunctionField (H := H) H.leadingCoeff := by
  simp [regularLeadingCoeff, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

@[simp] theorem piZ_regularLeadingCoeff (z : F) (root : rationalRoot (monicize H) z) :
    piZ z root (regularLeadingCoeff H) = H.leadingCoeff.eval z := by
  simp [regularLeadingCoeff, piZ_mk_C]

/-- The one element inverted in the place-local ring.  Inverting its product makes both `W` and
`xi` units while keeping the denominator accounting explicit. -/
noncomputable def denominatorBase (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  regularLeadingCoeff H * xi x₀ R H hHyp

/-- The ring in which all repaired Hensel coefficients are regular. -/
abbrev LocalRing (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :=
  Localization.Away (denominatorBase x₀ R H hHyp)

private theorem denominatorBase_embed_ne_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (denominatorBase x₀ R H hHyp) ≠ 0 := by
  rw [denominatorBase, map_mul, embed_regularLeadingCoeff,
    embeddingOf𝒪Into𝕃_xi x₀ R H hHyp]
  exact mul_ne_zero (liftToFunctionField_leadingCoeff_ne_zero (H := H))
    (mul_ne_zero
      (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H)))
      (zeta_ne_zero_of_hypotheses x₀ R H hHyp))

/-- The local ring embeds in the function field. -/
noncomputable def toFunctionField (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) : LocalRing x₀ R H hHyp →+* 𝕃 H :=
  IsLocalization.Away.lift (denominatorBase x₀ R H hHyp)
    (isUnit_iff_ne_zero.mpr (denominatorBase_embed_ne_zero x₀ R H hHyp))

@[simp] theorem toFunctionField_algebraMap (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (a : 𝒪 H) :
    toFunctionField x₀ R H hHyp (algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) a) =
      embeddingOf𝒪Into𝕃 H a := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- No new kernel is introduced by localizing the already embedded regular quotient. -/
theorem toFunctionField_injective (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    Function.Injective (toFunctionField x₀ R H hHyp) := by
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro hab
    have := congrArg (toFunctionField x₀ R H hHyp) hab
    simpa using this
  · intro hab
    have hab' : a = b := embeddingOf𝒪Into𝕃_injective hHpos.out hab
    simpa [hab']

private theorem leadingCoeff_isUnit (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    IsUnit (algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) (regularLeadingCoeff H)) := by
  apply IsLocalization.Away.isUnit_of_dvd
  exact dvd_mul_right (regularLeadingCoeff H) (xi x₀ R H hHyp)

private theorem xi_isUnit (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    IsUnit (algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) (xi x₀ R H hHyp)) := by
  apply IsLocalization.Away.isUnit_of_dvd
  exact dvd_mul_left (xi x₀ R H hHyp) (regularLeadingCoeff H)

/-- The inverse of a specified unit, usable in a ring without a global division operation. -/
noncomputable def unitInv {A : Type} [Monoid A] (a : A) (ha : IsUnit a) : A :=
  (ha.unit⁻¹ : Aˣ)

@[simp] theorem mul_unitInv {A : Type} [Monoid A] (a : A) (ha : IsUnit a) :
    a * unitInv a ha = 1 := by
  simp [unitInv]

@[simp] theorem unitInv_mul {A : Type} [Monoid A] (a : A) (ha : IsUnit a) :
    unitInv a ha * a = 1 := by
  simp [unitInv]

theorem map_unitInv {A B : Type} [Monoid A] [Monoid B] (f : A →* B)
    (a : A) (ha : IsUnit a) :
    f (unitInv a ha) = unitInv (f a) (ha.map f) := by
  simp [unitInv]

/-- A repaired Hensel coefficient represented in the local ring. -/
noncomputable def localAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (t : ℕ) : LocalRing x₀ R H hHyp :=
  let a := algebraMap (𝒪 H) (LocalRing x₀ R H hHyp)
  a (betaSeq x₀ R H hHyp t) *
    unitInv (a (regularLeadingCoeff H)) (leadingCoeff_isUnit x₀ R H hHyp) ^ (t + 1) *
    unitInv (a (xi x₀ R H hHyp)) (xi_isUnit x₀ R H hHyp) ^
      henselDenominatorExponent t

/-- The local representative maps to the selected function-field coefficient. -/
theorem toFunctionField_localAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    toFunctionField x₀ R H hHyp (localAlpha x₀ R H hHyp t) =
      alpha x₀ R H hHyp t := by
  let a := algebraMap (𝒪 H) (LocalRing x₀ R H hHyp)
  let Wloc := a (regularLeadingCoeff H)
  let xiloc := a (xi x₀ R H hHyp)
  have hWmap : toFunctionField x₀ R H hHyp Wloc =
      liftToFunctionField (H := H) H.leadingCoeff := by
    simp [Wloc, a]
  have hximap : toFunctionField x₀ R H hHyp xiloc =
      embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) := by
    simp [xiloc, a]
  have hWinv : toFunctionField x₀ R H hHyp
      (unitInv Wloc (leadingCoeff_isUnit x₀ R H hHyp)) =
        (liftToFunctionField (H := H) H.leadingCoeff)⁻¹ := by
    apply eq_inv_of_mul_right_eq_one
    rw [← map_mul, mul_unitInv, map_one, hWmap]
  have hxiinv : toFunctionField x₀ R H hHyp
      (unitInv xiloc (xi_isUnit x₀ R H hHyp)) =
        (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp))⁻¹ := by
    apply eq_inv_of_mul_right_eq_one
    rw [← map_mul, mul_unitInv, map_one, hximap]
  simp only [localAlpha, map_mul, map_pow, toFunctionField_algebraMap, hWinv, hxiinv,
    alpha, alphaOfNumerators, div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- Embed a coefficient polynomial in the local ring. -/
noncomputable def coefficientToLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) : F[X] →+* LocalRing x₀ R H hHyp :=
  (algebraMap (𝒪 H) (LocalRing x₀ R H hHyp)).comp
    ((Ideal.Quotient.mk (Ideal.span {monicize H})).comp Polynomial.C)

/-- Recenter the `X` variable while retaining generic `Z` in the local ring. -/
noncomputable def liftCoeffLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) : F[X][X] →+* PowerSeries (LocalRing x₀ R H hHyp) :=
  Polynomial.eval₂RingHom
    ((PowerSeries.C : LocalRing x₀ R H hHyp →+* PowerSeries (LocalRing x₀ R H hHyp)).comp
      (coefficientToLocal x₀ R H hHyp))
    (PowerSeries.C (coefficientToLocal x₀ R H hHyp (Polynomial.C x₀)) + PowerSeries.X)

noncomputable def evalRLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (Gamma : PowerSeries (LocalRing x₀ R H hHyp)) :
    PowerSeries (LocalRing x₀ R H hHyp) :=
  Polynomial.eval₂ (liftCoeffLocal x₀ R H hHyp) Gamma R

private theorem map_liftCoeffLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (p : F[X][X]) :
    PowerSeries.map (toFunctionField x₀ R H hHyp) (liftCoeffLocal x₀ R H hHyp p) =
      liftCoeffToPowerSeries x₀ H p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq, add_mul]
      | monomial m c =>
          simp [liftCoeffLocal, liftCoeffToPowerSeries, coefficientToLocal,
            toFunctionField_algebraMap, embeddingOf𝒪Into𝕃_mk, liftBivariate_C,
            fieldTo𝕃, Polynomial.coeToPowerSeries.ringHom_apply]

private theorem map_evalRLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (Gamma : PowerSeries (LocalRing x₀ R H hHyp)) :
    PowerSeries.map (toFunctionField x₀ R H hHyp) (evalRLocal x₀ R H hHyp Gamma) =
      evalRAtPowerSeries x₀ H R (PowerSeries.map (toFunctionField x₀ R H hHyp) Gamma) := by
  unfold evalRLocal evalRAtPowerSeries
  induction R using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p => simp [map_liftCoeffLocal]

/-- The local coefficient sequence is already a root before choosing a place. -/
theorem localAlpha_root (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    evalRLocal x₀ R H hHyp (PowerSeries.mk (localAlpha x₀ R H hHyp)) = 0 := by
  apply PowerSeries.map_injective (toFunctionField x₀ R H hHyp)
    (toFunctionField_injective x₀ R H hHyp)
  rw [map_evalRLocal, map_zero]
  have hseries : PowerSeries.map (toFunctionField x₀ R H hHyp)
      (PowerSeries.mk (localAlpha x₀ R H hHyp)) = gamma x₀ R H hHyp := by
    ext t
    simp [gamma, gammaOfNumerators, toFunctionField_localAlpha]
  rw [hseries]
  exact (betaSeq_spec x₀ R H hHyp).2

/-- Evaluation of the place-local ring at a good rational place. -/
noncomputable def toPlace (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hgood : piZ z root (denominatorBase x₀ R H hHyp) ≠ 0) :
    LocalRing x₀ R H hHyp →+* F :=
  IsLocalization.Away.lift (denominatorBase x₀ R H hHyp)
    (isUnit_iff_ne_zero.mpr hgood)

@[simp] theorem toPlace_algebraMap (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hgood : piZ z root (denominatorBase x₀ R H hHyp) ≠ 0) (a : 𝒪 H) :
    toPlace x₀ R H hHyp z root hgood
        (algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) a) = piZ z root a := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The scalar value of a Hensel coefficient at a good place. -/
noncomputable def alphaAt (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) (t : ℕ) : F :=
  piZ z root (betaSeq x₀ R H hHyp t) /
    (H.leadingCoeff.eval z ^ (t + 1) *
      piZ z root (xi x₀ R H hHyp) ^ henselDenominatorExponent t)

theorem denominatorBase_good (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) :
    piZ z root (denominatorBase x₀ R H hHyp) ≠ 0 := by
  simp [denominatorBase, hW, hxi]

theorem toPlace_localAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) (t : ℕ) :
    toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi)
        (localAlpha x₀ R H hHyp t) = alphaAt x₀ R H hHyp z root hW hxi t := by
  let a := algebraMap (𝒪 H) (LocalRing x₀ R H hHyp)
  let phi := toPlace x₀ R H hHyp z root
    (denominatorBase_good x₀ R H hHyp z root hW hxi)
  have hWinv : phi (unitInv (a (regularLeadingCoeff H))
      (leadingCoeff_isUnit x₀ R H hHyp)) = (H.leadingCoeff.eval z)⁻¹ := by
    apply eq_inv_of_mul_right_eq_one
    rw [← map_mul, mul_unitInv, map_one]
    simp [phi, a]
  have hxiinv : phi (unitInv (a (xi x₀ R H hHyp))
      (xi_isUnit x₀ R H hHyp)) = (piZ z root (xi x₀ R H hHyp))⁻¹ := by
    apply eq_inv_of_mul_right_eq_one
    rw [← map_mul, mul_unitInv, map_one]
    simp [phi, a]
  simp only [localAlpha, alphaAt, map_mul, map_pow, toPlace_algebraMap, hWinv, hxiinv,
    div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- Taylor recentering followed by the polynomial-to-power-series embedding. -/
noncomputable def recenterCoe (x₀ : F) : F[X] →+* PowerSeries F :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.taylorAlgHom x₀).toRingHom

theorem recenterCoe_apply (x₀ : F) (p : F[X]) :
    recenterCoe x₀ p = ((Polynomial.taylor x₀ p : F[X]) : PowerSeries F) := by
  simp [recenterCoe]

noncomputable def specializeR (R : F[X][X][Y]) (z : F) : F[X][Y] :=
  R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

noncomputable def recenteredR (x₀ : F) (R : F[X][X][Y]) (z : F) :
    Polynomial (PowerSeries F) :=
  (specializeR R z).map (recenterCoe x₀)

noncomputable def recenteredPolynomial (x₀ : F) (P : F[X]) : PowerSeries F :=
  recenterCoe x₀ P

@[simp] theorem coeff_recenteredPolynomial (x₀ : F) (P : F[X]) (t : ℕ) :
    PowerSeries.coeff t (recenteredPolynomial x₀ P) =
      (Polynomial.taylor x₀ P).coeff t := by
  simp [recenteredPolynomial, recenterCoe_apply]

theorem recenteredPolynomial_root {x₀ z : F} {R : F[X][X][Y]} {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣ specializeR R z) :
    Polynomial.eval (recenteredPolynomial x₀ P) (recenteredR x₀ R z) = 0 := by
  have hmap := Polynomial.map_dvd (recenterCoe x₀) hdvd
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at hmap
  exact Polynomial.dvd_iff_isRoot.mp hmap

private theorem map_liftCoeffLocal_toPlace (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) (p : F[X][X]) :
    PowerSeries.map
        (toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi))
        (liftCoeffLocal x₀ R H hHyp p) =
      recenterCoe x₀ (p.map (Polynomial.evalRingHom z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp, hq, add_mul]
      | monomial m c =>
          simp [liftCoeffLocal, coefficientToLocal, recenterCoe, toPlace_algebraMap,
            piZ_mk_C, Polynomial.coeToPowerSeries.ringHom_apply]

private theorem map_evalRLocal_toPlace (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0)
    (Gamma : PowerSeries (LocalRing x₀ R H hHyp)) :
    PowerSeries.map
        (toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi))
        (evalRLocal x₀ R H hHyp Gamma) =
      Polynomial.eval
        (PowerSeries.map
          (toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi))
          Gamma)
        (recenteredR x₀ R z) := by
  unfold evalRLocal recenteredR specializeR
  induction R using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n p => simp [map_liftCoeffLocal_toPlace]

theorem alphaAt_root (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) :
    Polynomial.eval (PowerSeries.mk (alphaAt x₀ R H hHyp z root hW hxi))
      (recenteredR x₀ R z) = 0 := by
  have h := congrArg
    (PowerSeries.map
      (toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi)))
    (localAlpha_root x₀ R H hHyp)
  rw [map_zero, map_evalRLocal_toPlace] at h
  convert h using 2
  ext t
  simp [toPlace_localAlpha]

private theorem betaSeq_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) :
    betaSeq x₀ R H hHyp 0 =
      (Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.X : F[X][Y]) : 𝒪 H) := by
  apply beta_zero_eq_X_of_shape x₀ R H hHyp hHpos.out
      (defaultDegreeBound_ge_H R H)
      (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)
      (alphaOfNumerators x₀ R H hHyp (betaSeq x₀ R H hHyp))
      (betaSeq x₀ R H hHyp)
  · exact (betaSeq_spec x₀ R H hHyp).1
  · exact (betaSeq_spec x₀ R H hHyp).2
  · intro t
    rfl

theorem alphaAt_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) :
    alphaAt x₀ R H hHyp z root hW hxi 0 = root.1 / H.leadingCoeff.eval z := by
  rw [alphaAt, betaSeq_zero x₀ R H hHyp]
  simp [piZ, piZLift, henselDenominatorExponent]

/-- The derivative of the recentered scalar equation is nonzero at the specialized Hensel root.
This is obtained by transporting `embed(xi) = W^(d-2) * zeta` through the place-local ring. -/
theorem derivative_ne_zero_at_alphaAt_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0) :
    Polynomial.eval (alphaAt x₀ R H hHyp z root hW hxi 0)
      (Polynomial.derivative
        (Series6317.constantPolynomial (recenteredR x₀ R z))) ≠ 0 := by
  intro hzero
  have hderivMap :
      Polynomial.eval (alphaAt x₀ R H hHyp z root hW hxi 0)
          (Polynomial.derivative
            (Series6317.constantPolynomial (recenteredR x₀ R z))) =
        piZ z root (xi x₀ R H hHyp) /
          H.leadingCoeff.eval z ^ (R.natDegree - 2) := by
    have hgeneric := embeddingOf𝒪Into𝕃_xi x₀ R H hHyp
    have hlocal :
        algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) (xi x₀ R H hHyp) =
          algebraMap (𝒪 H) (LocalRing x₀ R H hHyp) (regularLeadingCoeff H) ^
              (R.natDegree - 2) *
            Polynomial.eval (localAlpha x₀ R H hHyp 0)
              (Polynomial.derivative
                (Series6317.constantPolynomial
                  (R.map (liftCoeffLocal x₀ R H hHyp)))) := by
      apply toFunctionField_injective x₀ R H hHyp
      simp only [map_mul, map_pow, toFunctionField_algebraMap, hgeneric,
        toFunctionField_localAlpha]
      simp [Series6317.constantPolynomial, liftCoeffLocal, evalRAtPowerSeries,
        zeta, alpha, alphaOfNumerators]
    have hplace := congrArg
      (toPlace x₀ R H hHyp z root (denominatorBase_good x₀ R H hHyp z root hW hxi))
      hlocal
    simp only [map_mul, map_pow, toPlace_algebraMap] at hplace
    have hconstant :
        (Series6317.constantPolynomial
            (R.map (liftCoeffLocal x₀ R H hHyp))).map
            (toPlace x₀ R H hHyp z root
              (denominatorBase_good x₀ R H hHyp z root hW hxi)) =
          Series6317.constantPolynomial (recenteredR x₀ R z) := by
      ext i
      simp [Series6317.constantPolynomial, recenteredR, specializeR,
        map_liftCoeffLocal_toPlace]
    rw [← hconstant, Polynomial.derivative_map, Polynomial.eval_map,
      toPlace_localAlpha] at hplace
    rw [eq_div_iff (pow_ne_zero _ hW)]
    exact hplace.symm
  rw [hderivMap] at hzero
  exact hxi ((div_eq_zero_iff).mp hzero |>.resolve_right (pow_ne_zero _ hW))

/-- **Place coefficient reading.**  A decoded polynomial branch through the same rational point
has the Taylor coefficients obtained by specializing the repaired Hensel numerators. -/
theorem alphaAt_eq_taylorCoeff (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0)
    (P : F[X])
    (hbase : root.1 = H.leadingCoeff.eval z * P.eval x₀)
    (hdvd : Polynomial.X - Polynomial.C P ∣ specializeR R z) (t : ℕ) :
    alphaAt x₀ R H hHyp z root hW hxi t = (Polynomial.taylor x₀ P).coeff t := by
  have hcc : PowerSeries.constantCoeff
      (PowerSeries.mk (alphaAt x₀ R H hHyp z root hW hxi)) =
      PowerSeries.constantCoeff (recenteredPolynomial x₀ P) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      coeff_recenteredPolynomial, Polynomial.taylor_coeff_zero,
      alphaAt_zero x₀ R H hHyp z root hW hxi, hbase]
    field_simp [hW]
  have hu : IsUnit
      (Polynomial.eval
        (PowerSeries.constantCoeff (PowerSeries.mk (alphaAt x₀ R H hHyp z root hW hxi)))
        (Polynomial.derivative (Series6317.constantPolynomial (recenteredR x₀ R z)))) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact isUnit_iff_ne_zero.mpr
      (derivative_ne_zero_at_alphaAt_zero x₀ R H hHyp z root hW hxi)
  have heq := Series6317.root_unique (Q := recenteredR x₀ R z) hcc hu
    (alphaAt_root x₀ R H hHyp z root hW hxi)
    (recenteredPolynomial_root hdvd)
  have := congrArg (PowerSeries.coeff t) heq
  simpa using this

/-- Above the decoded degree, coefficient reading says precisely that the numerator vanishes at
the rational place; all clearing denominators are nonzero. -/
theorem piZ_betaSeq_eq_zero_of_degree_lt (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (z : F) (root : rationalRoot (monicize H) z)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hxi : piZ z root (xi x₀ R H hHyp) ≠ 0)
    (P : F[X]) (k t : ℕ) (hP : P.natDegree < k) (ht : k ≤ t)
    (hbase : root.1 = H.leadingCoeff.eval z * P.eval x₀)
    (hdvd : Polynomial.X - Polynomial.C P ∣ specializeR R z) :
    piZ z root (betaSeq x₀ R H hHyp t) = 0 := by
  have hread := alphaAt_eq_taylorCoeff x₀ R H hHyp z root hW hxi P hbase hdvd t
  have hcoeff : (Polynomial.taylor x₀ P).coeff t = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Polynomial.natDegree_taylor]
    exact hP.trans_le ht
  rw [hcoeff] at hread
  unfold alphaAt at hread
  exact (div_eq_zero_iff.mp hread).resolve_right
    (mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hxi))

end Place
end PlaceSpecialization
end ProximityPrize.SubmissionLower.RF6317
