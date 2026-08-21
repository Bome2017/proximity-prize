import ProximityPrize.SubmissionLower.BCHKSPairSetupConcrete

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Parameter-generic selected-pair setup used by the raw resultant path. -/
theorem setup_selected_pair_raw
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (DY DZ k DX : Nat) (hDZ : 0 < DZ)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ DY)
    (hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < DZ)
    (hRweightedX : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + k * j < DX)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ DY ∧ H.natDegree ≤ DY ∧
    Polynomial.Bivariate.totalDegree H ≤ DZ - 1 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ DZ - 1 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + k * j < DX) ∧
    Hypotheses x₀ R H := by
  have hRirr : Irreducible R :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hHR).irreducible
  have hRdvd : R ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ
  have hHd : H ∣ triSpecializeX R x₀ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHR
  have hRdeg : R.natDegree ≤ DY :=
    (Polynomial.natDegree_le_of_dvd hRdvd hQ).trans hQY
  have hRXeq : triSpecializeX R x₀ =
      Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  have hRX0 : triSpecializeX R x₀ ≠ 0 := by
    rw [hRXeq]
    exact hprim.ne_zero
  have hHdeg : H.natDegree ≤ DY :=
    (Polynomial.natDegree_le_of_dvd hHd hRX0).trans
      ((triSpecializeX_natDegree_le R x₀).trans hRdeg)
  have hRXtotal : Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ DZ - 1 := by
    have hlt := totalDegree_triSpecializeX_lt R x₀ DZ hDZ hRYZ
    omega
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0)
      (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul hA hC]
    exact Nat.le_add_right _ _
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hHtotal : Polynomial.Bivariate.totalDegree H ≤ DZ - 1 :=
    (totalDegree_le_of_dvd hH0 hRX0 hHd).trans hRXtotal
  have hHyp : Hypotheses x₀ R H := by
    refine ⟨?_, hprim.ne_zero, ?_⟩
    · simpa [hRXeq] using hHd
    · intro C hfac hCdeg
      let c₀ : Polynomial F := C.coeff 0
      have hCC : C = Polynomial.C c₀ :=
        Polynomial.eq_C_of_natDegree_le_zero hCdeg.le
      have hCdvd : Polynomial.C c₀ ∣
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
        refine ⟨H, ?_⟩
        calc
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R = H * C := hfac
          _ = H * Polynomial.C c₀ := by rw [hCC]
          _ = Polynomial.C c₀ * H := mul_comm _ _
      exact (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim) c₀ hCdvd
  exact ⟨hRirr, hHirr, hHpos, hHd, hRdeg, hHdeg,
    hHtotal, hRXtotal, hRweightedX, hHyp⟩

/-- Inherit both support caps from the interpolation polynomial before using
the generic setup. -/
theorem bchks_pair_setup_raw_of_selected_factors
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (DY DZ k DX : Nat) (hDZ : 0 < DZ)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ DY)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < DZ)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + k * j < DX)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ DY ∧ H.natDegree ≤ DY ∧
    Polynomial.Bivariate.totalDegree H ≤ DZ - 1 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ DZ - 1 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + k * j < DX) ∧
    Hypotheses x₀ R H := by
  have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R DZ hQ hRQ hQYZ
  have hRW := WeightedFactorCaps.normalizedFactor_weightedX_cap
    Q R k DX hQ hRQ hQweightedX
  exact setup_selected_pair_raw Q R H x₀ DY DZ k DX hDZ hQ hRQ hHR
    hHpos hQY hRYZ hRW hprim

end ProximityPrize.SubmissionLower
