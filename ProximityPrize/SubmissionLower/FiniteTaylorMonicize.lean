import ProximityPrize.SubmissionLower.FiniteTaylorCore
import ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale
import ProximityPrize.SubmissionLower.FiniteTaylorCoprimeDet

namespace ProximityPrize.SubmissionLower.FiniteTaylorMonicize

open Polynomial
open ProximityPrize.SubmissionLower.FiniteTaylorCore
open ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale
open ProximityPrize.SubmissionLower.FiniteTaylorCoprimeDet

noncomputable section

variable {F : Type*} [Field F]

/-- The algebraic core of integral monicization.  This is definitionally the
same expression as `FiniteTaylorExtraction.integralMonicize`, but is kept in a
small independently compilable module so its fraction-field properties do not
depend on the combinatorial extraction development. -/
def integralMonicizeAux (H : Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  let h := H.natDegree
  let W := H.leadingCoeff
  Polynomial.monomial h 1 +
    ∑ i ∈ Finset.range h,
      Polynomial.monomial i (H.coeff i * W ^ (h - 1 - i))

theorem integralMonicizeAux_coeff_top (H : Polynomial (Polynomial F)) :
    (integralMonicizeAux H).coeff H.natDegree = 1 := by
  classical
  simp only [integralMonicizeAux, coeff_add, coeff_monomial,
    Polynomial.finsetSum_coeff]
  simp

theorem integralMonicizeAux_natDegree_le (H : Polynomial (Polynomial F)) :
    (integralMonicizeAux H).natDegree ≤ H.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  classical
  simp only [integralMonicizeAux, coeff_add, coeff_monomial,
    Polynomial.finsetSum_coeff]
  have hne : H.natDegree ≠ n := by omega
  simp only [if_neg hne]
  rw [zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  have hilt : i < H.natDegree := Finset.mem_range.mp hi
  have hin : i ≠ n := by omega
  simp [hin]

theorem integralMonicizeAux_monic (H : Polynomial (Polynomial F)) :
    (integralMonicizeAux H).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one H.natDegree
    (integralMonicizeAux_natDegree_le H) (integralMonicizeAux_coeff_top H)

theorem integralMonicizeAux_natDegree (H : Polynomial (Polynomial F)) :
    (integralMonicizeAux H).natDegree = H.natDegree := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (integralMonicizeAux_natDegree_le H) (by
      rw [integralMonicizeAux_coeff_top]
      exact one_ne_zero)

theorem integralMonicizeAux_coeff_of_lt (H : Polynomial (Polynomial F))
    (i : ℕ) (hi : i < H.natDegree) :
    (integralMonicizeAux H).coeff i =
      H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i) := by
  classical
  simp only [integralMonicizeAux, coeff_add, coeff_monomial,
    Polynomial.finsetSum_coeff]
  have htop : H.natDegree ≠ i := by omega
  simp only [if_neg htop]
  rw [zero_add, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hi)).elim

/-- Clearing the leading coefficient turns the monicization into the standard
root scaling `W^h H(T/W)`. -/
theorem C_leadingCoeff_mul_integralMonicizeAux
    (H : Polynomial (Polynomial F)) :
    Polynomial.C H.leadingCoeff * integralMonicizeAux H =
      H.scaleRoots H.leadingCoeff := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < H.natDegree
  · rw [Polynomial.coeff_C_mul, integralMonicizeAux_coeff_of_lt H i hi,
      Polynomial.coeff_scaleRoots]
    have hpos : 0 < H.natDegree := Nat.zero_lt_of_lt hi
    have hexp : H.natDegree - 1 - i + 1 = H.natDegree - i := by omega
    calc
      H.leadingCoeff *
          (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i)) =
        H.coeff i * H.leadingCoeff ^
          (H.natDegree - 1 - i + 1) := by rw [pow_succ]; ring
      _ = H.coeff i * H.leadingCoeff ^ (H.natDegree - i) := by rw [hexp]
  · by_cases hitop : i = H.natDegree
    · subst i
      rw [Polynomial.coeff_C_mul, integralMonicizeAux_coeff_top,
        Polynomial.coeff_scaleRoots]
      simp [Polynomial.coeff_natDegree]
    · have hgt : H.natDegree < i := by omega
      have haux : (integralMonicizeAux H).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          ((integralMonicizeAux_natDegree_le H).trans_lt hgt)
      have hH : H.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hgt
      rw [Polynomial.coeff_C_mul, haux, mul_zero,
        Polynomial.coeff_scaleRoots, hH, zero_mul]

theorem integralMonicizeAux_polyHeight_le
    (H : Polynomial (Polynomial F)) (D : ℕ)
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ D) :
    polyHeight (integralMonicizeAux H) ≤ H.natDegree * D := by
  rw [polyHeight_le_iff]
  intro i
  by_cases hi : i < H.natDegree
  · rw [integralMonicizeAux_coeff_of_lt H i hi]
    calc
      (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i)).natDegree ≤
          (H.coeff i).natDegree +
            (H.leadingCoeff ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ D + (H.natDegree - 1 - i) * D := by
        apply Nat.add_le_add (hcoeff i)
        exact Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left _ (hcoeff H.natDegree))
      _ ≤ H.natDegree * D := by
        have : H.natDegree - 1 - i + 1 ≤ H.natDegree := by omega
        calc
          D + (H.natDegree - 1 - i) * D =
              (H.natDegree - 1 - i + 1) * D := by
                simp [Nat.add_mul, Nat.add_comm]
          _ ≤ H.natDegree * D := Nat.mul_le_mul_right D this
  · by_cases hitop : i = H.natDegree
    · subst i
      rw [integralMonicizeAux_coeff_top]
      simp
    · have hgt : H.natDegree < i := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((integralMonicizeAux_natDegree_le H).trans_lt hgt)]
      simp

theorem integralMonicizeAux_polyHeight_le_792
    (H : Polynomial (Polynomial F))
    (hdegree : H.natDegree ≤ 11)
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ 72) :
    polyHeight (integralMonicizeAux H) ≤ 792 := by
  exact (integralMonicizeAux_polyHeight_le H 72 hcoeff).trans (by omega)

/-- Integral monicization preserves irreducibility.  The proof maps to the
fraction field of `F[Z]`, where clearing the leading coefficient is a unit and
the construction is associated to a nonzero root scaling of `H`, then applies
the monic form of Gauss's lemma to descend. -/
theorem irreducible_integralMonicizeAux
    (H : Polynomial (Polynomial F))
    (hirr : Irreducible H) (hpos : 0 < H.natDegree) :
    Irreducible (integralMonicizeAux H) := by
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hW : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hφW : φ H.leadingCoeff ≠ 0 := fun hz =>
    hW (hφ (by simpa using hz))
  have hirrMap : Irreducible (H.map φ) := by
    have hprimitive := hirr.isPrimitive (Nat.ne_of_gt hpos)
    exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hscaled :
      Irreducible ((H.map φ).scaleRoots (φ H.leadingCoeff)) :=
    ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale.irreducible_scaleRoots
      (φ H.leadingCoeff) (H.map φ) hφW hirrMap
  have hid :
      Polynomial.C (φ H.leadingCoeff) *
          (integralMonicizeAux H).map φ =
        (H.map φ).scaleRoots (φ H.leadingCoeff) := by
    have hmapped := congrArg (Polynomial.map φ)
      (C_leadingCoeff_mul_integralMonicizeAux H)
    simpa [Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_scaleRoots H H.leadingCoeff φ hφW] using hmapped
  have hunitC :
      IsUnit (Polynomial.C (φ H.leadingCoeff) : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hφW)
  have hassociated :
      Associated ((integralMonicizeAux H).map φ)
        ((H.map φ).scaleRoots (φ H.leadingCoeff)) := by
    refine ⟨hunitC.unit, ?_⟩
    rw [hunitC.unit_spec]
    simpa [mul_comm] using hid
  have hirrAuxMap : Irreducible ((integralMonicizeAux H).map φ) :=
    hassociated.symm.irreducible hscaled
  exact Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (integralMonicizeAux_monic H) |>.mpr hirrAuxMap

/-- If `H` divides a separable ambient equation `P`, then after the common
root scaling by the leading coefficient of `H`, the integral monicization is
coprime to the derivative of the scaled ambient equation. -/
theorem integralMonicizeAux_map_isCoprime_scaledDerivative
    (H P : Polynomial (Polynomial F))
    (hpos : 0 < H.natDegree) (hHdvd : H ∣ P)
    (hsep : (P.map (algebraMap (Polynomial F)
      (FractionRing (Polynomial F)))).Separable)
    (hderivative :
      (P.map (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)))).derivative.natDegree =
        (P.map (algebraMap (Polynomial F)
          (FractionRing (Polynomial F)))).natDegree - 1) :
    IsCoprime
      ((integralMonicizeAux H).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F))))
      (((P.map (algebraMap (Polynomial F)
          (FractionRing (Polynomial F)))).scaleRoots
          ((algebraMap (Polynomial F) (FractionRing (Polynomial F)))
            H.leadingCoeff)).derivative) := by
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hpos
  have hW : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hφW : φ H.leadingCoeff ≠ 0 := fun hz =>
    hW (hφ (by simpa using hz))
  have hsepScaled :
      ((P.map φ).scaleRoots (φ H.leadingCoeff)).Separable :=
    ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale.scaleRoots_separable
      (φ H.leadingCoeff) (P.map φ) hφW hsep hderivative
  have hHmapDvd : H.map φ ∣ P.map φ := Polynomial.map_dvd φ hHdvd
  have hscaledDvd :
      (H.map φ).scaleRoots (φ H.leadingCoeff) ∣
        (P.map φ).scaleRoots (φ H.leadingCoeff) := by
    rcases hHmapDvd with ⟨G, hG⟩
    refine ⟨G.scaleRoots (φ H.leadingCoeff), ?_⟩
    rw [← Polynomial.mul_scaleRoots_of_noZeroDivisors]
    exact congrArg (fun Q : Polynomial K => Q.scaleRoots (φ H.leadingCoeff)) hG
  have hid :
      Polynomial.C (φ H.leadingCoeff) *
          (integralMonicizeAux H).map φ =
        (H.map φ).scaleRoots (φ H.leadingCoeff) := by
    have hmapped := congrArg (Polynomial.map φ)
      (C_leadingCoeff_mul_integralMonicizeAux H)
    simpa [Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_scaleRoots H H.leadingCoeff φ hφW] using hmapped
  have hauxDvdHscaled :
      (integralMonicizeAux H).map φ ∣
        (H.map φ).scaleRoots (φ H.leadingCoeff) := by
    refine ⟨Polynomial.C (φ H.leadingCoeff), ?_⟩
    simpa [mul_comm] using hid.symm
  have hauxDvdScaled :
      (integralMonicizeAux H).map φ ∣
        (P.map φ).scaleRoots (φ H.leadingCoeff) :=
    dvd_trans hauxDvdHscaled hscaledDvd
  exact ((Polynomial.separable_def _).mp hsepScaled).of_isCoprime_of_dvd_left
    hauxDvdScaled

/-- Determinant form of the preceding coprimality bridge.  A concrete Taylor
development only has to identify its integralized derivative `J` with the
derivative of the scaled ambient equation after passage to the fraction field. -/
theorem det_multiplicationMatrix_integralMonicizeAux_ne_zero
    (H P J : Polynomial (Polynomial F))
    (hpos : 0 < H.natDegree) (hHdvd : H ∣ P)
    (hsep : (P.map (algebraMap (Polynomial F)
      (FractionRing (Polynomial F)))).Separable)
    (hderivative :
      (P.map (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)))).derivative.natDegree =
        (P.map (algebraMap (Polynomial F)
          (FractionRing (Polynomial F)))).natDegree - 1)
    (hJ : J.map (algebraMap (Polynomial F)
        (FractionRing (Polynomial F))) =
      ((P.map (algebraMap (Polynomial F)
        (FractionRing (Polynomial F)))).scaleRoots
        ((algebraMap (Polynomial F) (FractionRing (Polynomial F)))
          H.leadingCoeff)).derivative) :
    (multiplicationMatrix H.natDegree (integralMonicizeAux H) J).det ≠ 0 := by
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hcoprime : IsCoprime
      ((integralMonicizeAux H).map φ) (J.map φ) := by
    rw [hJ]
    exact integralMonicizeAux_map_isCoprime_scaledDerivative
      H P hpos hHdvd hsep hderivative
  exact det_multiplicationMatrix_ne_zero_of_map_isCoprime
    φ hφ H.natDegree hpos (integralMonicizeAux H) J
    (integralMonicizeAux_monic H) (integralMonicizeAux_natDegree H) hcoprime

end

end ProximityPrize.SubmissionLower.FiniteTaylorMonicize
