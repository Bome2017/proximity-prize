import ProximityPrize.SubmissionLower.FiniteTaylorExtraction
import ProximityPrize.SubmissionLower.FiniteTaylorMonicize
import ProximityPrize.SubmissionLower.SequentialFactorSelection

namespace ProximityPrize.SubmissionLower.FiniteTaylorFactorQBridge

open Polynomial
open ProximityPrize.SubmissionLower.FiniteTaylorCore
open ProximityPrize.SubmissionLower.FiniteTaylorExtraction
open ProximityPrize.SubmissionLower.FiniteTaylorMonicize
open ProximityPrize.SubmissionLower.SequentialFactorSelection
open ProximityPrize.Benchmark

noncomputable section

variable {F : Type} [Field F]

theorem integralMonicize_eq_integralMonicizeAux
    (H : Polynomial (Polynomial F)) :
    integralMonicize H = integralMonicizeAux H := by
  rfl

theorem integralMonicize_irreducible
    (H : Polynomial (Polynomial F))
    (hirr : Irreducible H) (hpos : 0 < H.natDegree) :
    Irreducible (integralMonicize H) := by
  rw [integralMonicize_eq_integralMonicizeAux]
  exact irreducible_integralMonicizeAux H hirr hpos

theorem integralMonicize_polyHeight_le
    (H : Polynomial (Polynomial F)) (D : ℕ)
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ D) :
    polyHeight (integralMonicize H) ≤ H.natDegree * D := by
  rw [integralMonicize_eq_integralMonicizeAux]
  exact integralMonicizeAux_polyHeight_le H D hcoeff

theorem integralMonicize_polyHeight_le_792
    (H : Polynomial (Polynomial F))
    (hdegree : H.natDegree ≤ 11)
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ 72) :
    polyHeight (integralMonicize H) ≤ 792 := by
  rw [integralMonicize_eq_integralMonicizeAux]
  exact integralMonicizeAux_polyHeight_le_792 H hdegree hcoeff

theorem map_integralScale_of_natDegree_eq
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (W : A) (R : Polynomial A)
    (hdegree : (R.map f).natDegree = R.natDegree) :
    (integralScale W R).map f = integralScale (f W) (R.map f) := by
  classical
  unfold integralScale
  rw [hdegree]
  change (Polynomial.mapRingHom f)
      (∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.monomial i (R.coeff i * W ^ (R.natDegree - i))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem map_integralScale_eq_integralScaleAt
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (W : A) (R : Polynomial A) :
    (integralScale W R).map f =
      FiniteTaylorIntegralScale.integralScaleAt R.natDegree (f W) (R.map f) := by
  classical
  unfold integralScale FiniteTaylorIntegralScale.integralScaleAt
  change (Polynomial.mapRingHom f)
      (∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.monomial i (R.coeff i * W ^ (R.natDegree - i))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem derivativeAtX_integralScale_eq_derivative_integralScale
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree) :
    derivativeAtX x₀ (integralScale (Polynomial.C W) R) =
      (integralScale W (specializeX x₀ R)).derivative := by
  let f : Polynomial (Polynomial F) →+* Polynomial F :=
    Polynomial.evalRingHom (Polynomial.C x₀)
  have hmap :
      (integralScale (Polynomial.C W) R).map f =
        integralScale W (specializeX x₀ R) := by
    simpa [f, specializeX] using
      map_integralScale_of_natDegree_eq f (Polynomial.C W) R hdegree
  rw [derivativeAtX, ← Polynomial.derivative_map, hmap]

/-- The concrete derivative used by the Taylor quotient is exactly the
derivative of the root-scaled specialization at `X=x₀`. -/
theorem derivativeAtX_integralScale_eq_derivative_scaleRoots
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree) :
    derivativeAtX x₀ (integralScale (Polynomial.C W) R) =
      ((specializeX x₀ R).scaleRoots W).derivative := by
  let f : Polynomial (Polynomial F) →+* Polynomial F :=
    Polynomial.evalRingHom (Polynomial.C x₀)
  have hmap :
      (integralScale (Polynomial.C W) R).map f =
        integralScale W (specializeX x₀ R) := by
    simpa [f, specializeX] using
      map_integralScale_of_natDegree_eq f (Polynomial.C W) R hdegree
  rw [derivativeAtX_integralScale_eq_derivative_integralScale
    x₀ W R hdegree]
  have hscale := FiniteTaylorIntegralScale.integralScaleAt_eq_scaleRoots
    (specializeX x₀ R).natDegree W (specializeX x₀ R) rfl
  exact congrArg Polynomial.derivative (by
    simpa [integralScale, FiniteTaylorIntegralScale.integralScaleAt] using hscale)

theorem specializeZ_derivativeAtX_integralScale
    (x₀ z : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree) :
    specializeZ z
        (derivativeAtX x₀ (integralScale (Polynomial.C W) R)) =
      (FiniteTaylorIntegralScale.integralScaleAt R.natDegree (W.eval z)
        (specializeZ z (specializeX x₀ R))).derivative := by
  rw [derivativeAtX_integralScale_eq_derivative_integralScale
    x₀ W R hdegree]
  unfold specializeZ
  rw [← Polynomial.derivative_map]
  simpa [hdegree] using congrArg Polynomial.derivative
    (map_integralScale_eq_integralScaleAt
      (Polynomial.evalRingHom z) W (specializeX x₀ R))

theorem map_derivativeAtX_integralScale_eq_derivative_scaleRoots
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hpositive : 0 < R.natDegree)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree) :
    (derivativeAtX x₀ (integralScale (Polynomial.C W) R)).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F))) =
      ((fractionMap (specializeX x₀ R)).scaleRoots
        ((algebraMap (Polynomial F) (FractionRing (Polynomial F))) W)).derivative := by
  let φ : Polynomial F →+* FractionRing (Polynomial F) :=
    algebraMap (Polynomial F) (FractionRing (Polynomial F))
  have hWinj : Function.Injective φ := IsFractionRing.injective _ _
  have hPne : specializeX x₀ R ≠ 0 := by
    intro hz
    have : (specializeX x₀ R).natDegree = 0 := by simp [hz]
    omega
  have hleadMap :
      φ (specializeX x₀ R).leadingCoeff ≠ 0 := by
    apply fun hz => Polynomial.leadingCoeff_ne_zero.mpr hPne (hWinj (by simpa using hz))
  rw [derivativeAtX_integralScale_eq_derivative_scaleRoots x₀ W R hdegree]
  rw [← Polynomial.derivative_map]
  rw [Polynomial.map_scaleRoots _ _ _ hleadMap]
  rfl

theorem irsField_natCast_ne_zero_of_pos_le_eleven
    {n : ℕ} (hn : 0 < n) (hle : n ≤ 11) :
    (n : IRSProfile.Field) ≠ 0 := by
  have hnbase : (n : KoalaBear.Field) ≠ 0 := by
    intro hzero
    have hdiv : KoalaBear.fieldSize ∣ n :=
      (CharP.cast_eq_zero_iff KoalaBear.Field KoalaBear.fieldSize n).mp hzero
    have hbig : KoalaBear.fieldSize ≤ n := Nat.le_of_dvd hn hdiv
    norm_num [KoalaBear.fieldSize] at hbig
    omega
  intro hzero
  have hcoeff := congrArg (fun a : IRSProfile.Field =>
    CompPoly.Extension.Ext.coeff a (0 : Fin 6)) hzero
  simp only [CompPoly.Extension.Ext.coeff_natCast,
    CompPoly.Extension.Ext.coeff_zero, Fin.val_zero, if_pos] at hcoeff
  exact hnbase hcoeff

theorem fractionMap_derivative_natDegree_eq_sub_one
    (P : Polynomial (Polynomial IRSProfile.Field))
    (hpos : 0 < P.natDegree) (hle : P.natDegree ≤ 11) :
    (fractionMap P).derivative.natDegree =
      (fractionMap P).natDegree - 1 := by
  let φ : Polynomial IRSProfile.Field →+*
      FractionRing (Polynomial IRSProfile.Field) :=
    algebraMap (Polynomial IRSProfile.Field)
      (FractionRing (Polynomial IRSProfile.Field))
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hncastF : (P.natDegree : IRSProfile.Field) ≠ 0 :=
    irsField_natCast_ne_zero_of_pos_le_eleven hpos hle
  have hncast : (P.natDegree : Polynomial IRSProfile.Field) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hncastF
  have hlead : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hpos)
  have hbase : P.derivative.natDegree = P.natDegree - 1 := by
    apply le_antisymm (Polynomial.natDegree_derivative_le P)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hpos]
    norm_cast
    simpa only [Nat.sub_add_cancel hpos, Polynomial.coeff_natDegree] using
      mul_ne_zero hlead hncast
  change (P.map φ).derivative.natDegree = (P.map φ).natDegree - 1
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hφ,
    Polynomial.natDegree_map_eq_of_injective hφ]
  exact hbase

/-- Fixed-size resultant cutting out specializations at which the ambient
`Y`-equation has a multiple root. -/
def simpleRootResultant
    (P : Polynomial (Polynomial F)) : Polynomial F :=
  Polynomial.resultant P P.derivative P.natDegree (P.natDegree - 1)

theorem simpleRootResultant_eval_derivative_ne_zero
    (P : Polynomial (Polynomial F)) (z y : F)
    (hPpos : 0 < P.natDegree)
    (hy : (specializeZ z P).eval y = 0)
    (hres : (simpleRootResultant P).eval z ≠ 0) :
    (specializeZ z P).derivative.eval y ≠ 0 := by
  let Pz := specializeZ z P
  change Pz.eval y = 0 at hy
  have hPzdeg : Pz.natDegree ≤ P.natDegree := by
    exact Polynomial.natDegree_map_le
  have hPzderivdeg : Pz.derivative.natDegree ≤ P.natDegree - 1 :=
    (Polynomial.natDegree_derivative_le Pz).trans
      (Nat.sub_le_sub_right hPzdeg 1)
  have hfixed : Polynomial.resultant Pz Pz.derivative
      P.natDegree (P.natDegree - 1) ≠ 0 := by
    intro hzero
    apply hres
    change (Polynomial.evalRingHom z) (simpleRootResultant P) = 0
    unfold simpleRootResultant
    dsimp [Pz, specializeZ] at hzero
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map] at hzero
    exact hzero
  intro hderiv
  change Pz.derivative.eval y = 0 at hderiv
  obtain ⟨a, b, _ha, _hb, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      Pz Pz.derivative hPzdeg hPzderivdeg (Or.inl (Nat.ne_of_gt hPpos))
  have heval := congrArg (Polynomial.evalRingHom y) hbezout
  simp [hy, hderiv] at heval
  exact hfixed heval.symm

/-- At any retained specialization where the ambient simple-root resultant
and `W` are nonzero, every retained `H`-root has nonzero integralized
derivative.  This supplies the `hJ` premise of finite Taylor extraction. -/
theorem concrete_integralizedDerivative_eval_ne_zero
    (x₀ z y : F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (H : Polynomial (Polynomial F))
    (hRpos : 0 < R.natDegree)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree)
    (hHdvd : H ∣ specializeX x₀ R)
    (hHroot : (specializeZ z H).eval y = 0)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hres : (simpleRootResultant (specializeX x₀ R)).eval z ≠ 0) :
    (specializeZ z (derivativeAtX x₀
      (integralScale (Polynomial.C H.leadingCoeff) R))).eval
        (H.leadingCoeff.eval z * y) ≠ 0 := by
  let P := specializeX x₀ R
  let Pz := specializeZ z P
  have hPzdeg : Pz.natDegree ≤ R.natDegree := by
    exact Polynomial.natDegree_map_le.trans_eq hdegree
  have hHPmap : specializeZ z H ∣ Pz := by
    exact Polynomial.map_dvd (Polynomial.evalRingHom z) hHdvd
  have hProot : Pz.eval y = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hHPmap hHroot
  have hPderiv : Pz.derivative.eval y ≠ 0 := by
    have hPpos : 0 < P.natDegree := by simp only [P]; omega
    exact simpleRootResultant_eval_derivative_ne_zero P z y hPpos hProot hres
  rw [specializeZ_derivativeAtX_integralScale x₀ z H.leadingCoeff R hdegree]
  exact FiniteTaylorIntegralScale.integralScaleAt_derivative_eval_ne_zero
    R.natDegree (H.leadingCoeff.eval z) y Pz hRpos hPzdeg hW hPderiv

theorem concrete_derivativeAtX_natDegree_le_ten
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hRdegree : R.natDegree ≤ 11)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree) :
    (derivativeAtX x₀ (integralScale (Polynomial.C W) R)).natDegree ≤ 10 := by
  rw [derivativeAtX_integralScale_eq_derivative_scaleRoots x₀ W R hdegree]
  calc
    ((specializeX x₀ R).scaleRoots W).derivative.natDegree ≤
        ((specializeX x₀ R).scaleRoots W).natDegree - 1 :=
      Polynomial.natDegree_derivative_le _
    _ = (specializeX x₀ R).natDegree - 1 := by
      rw [Polynomial.natDegree_scaleRoots]
    _ ≤ 10 := by omega

theorem concrete_derivativeAtX_polyHeight_le_864
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hRdegree : R.natDegree ≤ 11)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree)
    (hPcoeff : ∀ i,
      ((specializeX x₀ R).coeff i).natDegree ≤ 72)
    (hWdegree : W.natDegree ≤ 72) :
    polyHeight (derivativeAtX x₀
      (integralScale (Polynomial.C W) R)) ≤ 864 := by
  rw [derivativeAtX_integralScale_eq_derivative_scaleRoots x₀ W R hdegree]
  rw [polyHeight_le_iff]
  intro i
  rw [Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots]
  calc
    (((specializeX x₀ R).coeff (i + 1) *
          W ^ ((specializeX x₀ R).natDegree - (i + 1))) *
        (i + 1 : Polynomial F)).natDegree ≤
      ((specializeX x₀ R).coeff (i + 1) *
          W ^ ((specializeX x₀ R).natDegree - (i + 1))).natDegree +
        (i + 1 : Polynomial F).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 72 +
        ((specializeX x₀ R).natDegree - (i + 1)) * 72 + 0 := by
      apply Nat.add_le_add
      · exact Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (hPcoeff (i + 1))
            (Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul_left _ hWdegree)))
      · exact Nat.le_of_eq (by
          simpa only [map_add, map_one, Polynomial.C_eq_natCast] using
            (Polynomial.natDegree_C ((i : F) + 1)))
    _ ≤ 864 := by
      have hPdeg : (specializeX x₀ R).natDegree ≤ 11 := by omega
      have hexp : (specializeX x₀ R).natDegree - (i + 1) ≤ 11 := by omega
      omega

theorem polyHeight_shiftXCoefficient_le
    (x₀ : F) (A : Polynomial (Polynomial F)) (D : ℕ)
    (hA : polyHeight A ≤ D) :
    polyHeight (shiftXCoefficient x₀ A) ≤ D := by
  have hshift : polyHeight
      (Polynomial.X + Polynomial.C (Polynomial.C x₀) :
        Polynomial (Polynomial F)) ≤ 0 := by
    rw [polyHeight_le_iff]
    intro i
    rcases i with _ | i
    · simp
    · rcases i with _ | i
      · simp
      · simp [Polynomial.coeff_X]
  rw [polyHeight_le_iff]
  intro j
  unfold shiftXCoefficient
  change ((Polynomial.eval₂ Polynomial.C
    (Polynomial.X + Polynomial.C (Polynomial.C x₀)) A).coeff j).natDegree ≤ D
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hpow : polyHeight
      ((Polynomial.X + Polynomial.C (Polynomial.C x₀) :
        Polynomial (Polynomial F)) ^ i) ≤ 0 :=
    (polyHeight_pow_le _ i).trans (by
      rw [Nat.eq_zero_of_le_zero hshift, Nat.mul_zero])
  exact (natDegree_coeff_le_height _ j).trans
    ((polyHeight_mul_le _ _).trans (by
      rw [polyHeight_C]
      exact Nat.add_le_add
        ((natDegree_coeff_le_height A i).trans hA)
        hpow))

theorem concrete_shiftX_integralScale_natDegree_le_eleven
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hRdegree : R.natDegree ≤ 11) :
    (shiftX x₀ (integralScale (Polynomial.C W) R)).natDegree ≤ 11 := by
  exact Polynomial.natDegree_map_le.trans
    ((by
      have hscale := FiniteTaylorIntegralScale.integralScaleAt_eq_scaleRoots
        R.natDegree (Polynomial.C W) R rfl
      have heq : integralScale (Polynomial.C W) R =
          R.scaleRoots (Polynomial.C W) := by
        simpa [integralScale, FiniteTaylorIntegralScale.integralScaleAt] using hscale
      rw [heq, Polynomial.natDegree_scaleRoots]
      exact hRdegree) :
      (integralScale (Polynomial.C W) R).natDegree ≤ 11)

theorem concrete_shiftX_integralScale_coeff_polyHeight_le_864
    (x₀ : F) (W : Polynomial F)
    (R : SequentialFactorSelection.TriPolynomial F)
    (hRdegree : R.natDegree ≤ 11)
    (hRcoeff : ∀ j, polyHeight (R.coeff j) ≤ 72)
    (hWdegree : W.natDegree ≤ 72) (j : ℕ) :
    polyHeight
      ((shiftX x₀ (integralScale (Polynomial.C W) R)).coeff j) ≤ 864 := by
  have hscale := FiniteTaylorIntegralScale.integralScaleAt_eq_scaleRoots
    R.natDegree (Polynomial.C W) R rfl
  have heq : integralScale (Polynomial.C W) R =
      R.scaleRoots (Polynomial.C W) := by
    simpa [integralScale, FiniteTaylorIntegralScale.integralScaleAt] using hscale
  rw [shiftX, Polynomial.coeff_map, heq, Polynomial.coeff_scaleRoots]
  apply polyHeight_shiftXCoefficient_le x₀ _ 864
  calc
    polyHeight (R.coeff j *
        Polynomial.C W ^ (R.natDegree - j)) ≤
      polyHeight (R.coeff j) +
        polyHeight (Polynomial.C W ^ (R.natDegree - j)) :=
      polyHeight_mul_le _ _
    _ ≤ 72 + (R.natDegree - j) * 72 := by
      exact Nat.add_le_add (hRcoeff j)
        ((polyHeight_pow_le _ _).trans
          (Nat.mul_le_mul_left _ (by simpa [polyHeight_C] using hWdegree)))
    _ ≤ 864 := by
      have : R.natDegree - j ≤ 11 := by omega
      omega

/-- Fully concrete nonvanishing of the Taylor denominator polynomial.  The
hypotheses are precisely the data produced by the good-`x₀` factor-selection
branch: degree preservation, separability resultant, and an irreducible factor
dividing the specialized ambient equation. -/
theorem concrete_taylorDet_ne_zero
    (x₀ : IRSProfile.Field)
    (R : SequentialFactorSelection.TriPolynomial IRSProfile.Field)
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hRpos : 0 < R.natDegree) (hRle : R.natDegree ≤ 11)
    (hdegree : (specializeX x₀ R).natDegree = R.natDegree)
    (hresultant :
      (derivativeResultant R).eval (Polynomial.C x₀) ≠ 0)
    (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ specializeX x₀ R) :
    (multiplicationMatrix H.natDegree (integralMonicize H)
      (derivativeAtX x₀
        (integralScale (Polynomial.C H.leadingCoeff) R))).det ≠ 0 := by
  let P := specializeX x₀ R
  let J := derivativeAtX x₀
    (integralScale (Polynomial.C H.leadingCoeff) R)
  have hPpos : 0 < P.natDegree := by simp only [P]; omega
  have hPle : P.natDegree ≤ 11 := by simp only [P]; omega
  have hsep : (fractionMap P).Separable := by
    exact fractionMap_specializeX_separable R x₀ hRpos hresultant
  have hderivative : (fractionMap P).derivative.natDegree =
      (fractionMap P).natDegree - 1 :=
    fractionMap_derivative_natDegree_eq_sub_one P hPpos hPle
  have hJ : J.map (algebraMap (Polynomial IRSProfile.Field)
        (FractionRing (Polynomial IRSProfile.Field))) =
      ((fractionMap P).scaleRoots
        ((algebraMap (Polynomial IRSProfile.Field)
          (FractionRing (Polynomial IRSProfile.Field)))
            H.leadingCoeff)).derivative := by
    exact map_derivativeAtX_integralScale_eq_derivative_scaleRoots
      x₀ H.leadingCoeff R hRpos hdegree
  have haux := det_multiplicationMatrix_integralMonicizeAux_ne_zero
    H P J hHpos (by simpa [P] using hHdvd) hsep hderivative hJ
  simpa [J, integralMonicize_eq_integralMonicizeAux] using haux

end

end ProximityPrize.SubmissionLower.FiniteTaylorFactorQBridge
