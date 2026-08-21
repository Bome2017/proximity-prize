import ProximityPrize.SubmissionLower.Cap72Interpolation
import ProximityPrize.SubmissionLower.SequentialFactorSelection
import ProximityPrize.SubmissionLower.FiniteTaylorResultantRigidity

/-!
# Audited degree and separability bounds for a Cap72 factor

This file closes the field-specific algebraic obligations of the first
factor-specialization step.  The key grading is obtained by swapping the
inner variables `Z` and `X`: a polynomial in `F[Z][X][Y]` becomes a bivariate
polynomial in `(Z,Y)` over the domain `F[X]`.  Exact additivity of bivariate
total degree then makes the `Z+Y` cap hereditary under divisibility.
-/

namespace ProximityPrize.SubmissionLower.Cap72FactorAudit

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

noncomputable section

/-- Swap `Z` and `X` inside every outer-`Y` coefficient.  Semantically this
turns `F[Z][X][Y]` into `F[X][Z][Y]`, so bivariate total degree is `deg_Z+deg_Y`. -/
def swapZX {F : Type} [CommSemiring F] :
    Polynomial (Polynomial (Polynomial F)) →+*
      Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.mapRingHom (Polynomial.Bivariate.swap (R := F)).toRingHom

@[simp] theorem swapZX_monomial {F : Type} [CommSemiring F]
    (y x z : ℕ) (a : F) :
    swapZX (Polynomial.monomial y
      (Polynomial.monomial x (Polynomial.monomial z a))) =
      Polynomial.monomial y
        (Polynomial.monomial z (Polynomial.monomial x a)) := by
  simp [swapZX, Polynomial.Bivariate.swap_monomial_monomial]

theorem swapZX_injective {F : Type} [CommSemiring F] :
    Function.Injective (swapZX (F := F)) := by
  exact Polynomial.map_injective _
    (Polynomial.Bivariate.swap (R := F)).injective

theorem swapZX_ne_zero {F : Type} [CommSemiring F]
    {P : Polynomial (Polynomial (Polynomial F))} (hP : P ≠ 0) :
    swapZX P ≠ 0 :=
  fun h => hP (swapZX_injective (F := F) (h.trans (map_zero _).symm))

/-- Every Cap72 monomial has swapped `(Z,Y)` total degree at most `72`. -/
theorem totalDegree_swapZX_monomial_le
    {F : Type} [Field F] (q : Cap72.MonomialIndex) (a : F) :
    Polynomial.Bivariate.totalDegree
      (swapZX (Cap72.monomial q a)) ≤ 72 := by
  classical
  letI := Classical.decEq F
  rw [Cap72.monomial, swapZX_monomial]
  by_cases ha : a = 0
  · simp [ha, Polynomial.Bivariate.totalDegree]
  · have hcoeff : Polynomial.monomial (Cap72.xDegree q) a ≠ 0 := by simp [ha]
    simpa [Polynomial.Bivariate.monomialXY_def] using
      (Polynomial.Bivariate.totalDegree_monomialXY
        (n := Cap72.zDegree q) (m := Cap72.yDegree q) hcoeff |>.trans_le
          (Cap72.zDegree_add_yDegree_le q))

/-- The swapped Cap72 interpolant has `(Z,Y)` total degree at most `72`. -/
theorem totalDegree_swapZX_toPolynomial_le
    {F : Type} [Field F] (v : Cap72.MonomialIndex → F) :
    Polynomial.Bivariate.totalDegree (swapZX (Cap72.toPolynomial v)) ≤ 72 := by
  classical
  rw [Polynomial.Bivariate.total_deg_as_weighted_deg]
  unfold Cap72.toPolynomial
  rw [map_sum]
  refine (Polynomial.Bivariate.natWeightedDegree_sum_le Finset.univ
    (fun q => swapZX (Cap72.monomial q (v q))) 1 1).trans ?_
  apply Finset.sup_le
  intro q hq
  simpa [← Polynomial.Bivariate.total_deg_as_weighted_deg] using
    totalDegree_swapZX_monomial_le q (v q)

theorem Interpolant.totalDegree_swapZX_le
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v) :
    Polynomial.Bivariate.totalDegree (swapZX Q.polynomial) ≤ 72 :=
  totalDegree_swapZX_toPolynomial_le Q.coefficients

/-- Exact total-degree additivity makes the Cap72 `(Z,Y)` cap hereditary to
every nonzero divisor. -/
theorem factor_totalDegree_swapZX_le
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) :
    Polynomial.Bivariate.totalDegree (swapZX R) ≤ 72 := by
  obtain ⟨K, hQ⟩ := hR
  have hK0 : K ≠ 0 := by
    intro hK
    apply Q.polynomial_ne_zero
    rw [hK, mul_zero] at hQ
    exact hQ
  have hswapR : swapZX R ≠ 0 := swapZX_ne_zero hR0
  have hswapK : swapZX K ≠ 0 := swapZX_ne_zero hK0
  have hmul : swapZX Q.polynomial = swapZX R * swapZX K := by
    rw [hQ, map_mul]
  have hexact := Polynomial.Bivariate.totalDegree_mul
    (F := Polynomial F) hswapR hswapK
  rw [← hmul] at hexact
  calc
    Polynomial.Bivariate.totalDegree (swapZX R)
        ≤ Polynomial.Bivariate.totalDegree (swapZX R) +
            Polynomial.Bivariate.totalDegree (swapZX K) := Nat.le_add_right _ _
    _ = Polynomial.Bivariate.totalDegree (swapZX Q.polynomial) := hexact.symm
    _ ≤ 72 := Interpolant.totalDegree_swapZX_le Q

/-- Every `X`-degree in a factor is bounded by the Cap72 weighted-degree cap. -/
theorem factor_degreeX_le
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) :
    Polynomial.Bivariate.degreeX R ≤ 1760955 := by
  obtain ⟨K, hQ⟩ := hR
  have hK0 : K ≠ 0 := by
    intro hK
    apply Q.polynomial_ne_zero
    rw [hK, mul_zero] at hQ
    exact hQ
  have hexact := Polynomial.Bivariate.degreeX_mul R K hR0 hK0
  rw [← hQ] at hexact
  calc
    Polynomial.Bivariate.degreeX R
        ≤ Polynomial.Bivariate.degreeX R + Polynomial.Bivariate.degreeX K :=
          Nat.le_add_right _ _
    _ = Polynomial.Bivariate.degreeX Q.polynomial := hexact.symm
    _ ≤ Polynomial.Bivariate.natWeightedDegree Q.polynomial 1 131071 :=
      Polynomial.Bivariate.degreeX_le_natWeightedDegree Q.polynomial 131071
    _ ≤ 1760955 := Q.polynomial_natWeightedDegree_le

/-- The outer `Y` degree of a factor is at most eleven. -/
theorem factor_natDegree_le_eleven
    {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) : R.natDegree ≤ 11 :=
  (Polynomial.natDegree_le_of_dvd hR Q.polynomial_ne_zero).trans
    Q.polynomial_natDegree_le

/-- Each `X`-polynomial coefficient is bounded by bivariate `degreeX`. -/
theorem coeff_natDegree_le_degreeX
    {A : Type} [Semiring A] (P : Polynomial (Polynomial A)) (i : ℕ) :
    (P.coeff i).natDegree ≤ Polynomial.Bivariate.degreeX P := by
  classical
  by_cases hi : i ∈ P.support
  · unfold Polynomial.Bivariate.degreeX
    exact Finset.le_sup (f := fun j => (P.coeff j).natDegree) hi
  · rw [Polynomial.notMem_support_iff.mp hi, Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- Consequently every nested `X` coefficient of the factor is bounded. -/
theorem factor_coeff_natDegree_le
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) (i : ℕ) :
    (R.coeff i).natDegree ≤ 1760955 :=
  (coeff_natDegree_le_degreeX R i).trans (factor_degreeX_le Q hR hR0)

/-- The characteristic of the concrete IRS field is the KoalaBear prime. -/
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

/-- For positive outer degree at most eleven, the formal derivative is
nonzero over the concrete IRS field (and hence over its polynomial rings). -/
theorem derivative_ne_zero_of_pos_le_eleven
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hpos : 0 < R.natDegree) (hle : R.natDegree ≤ 11) :
    R.derivative ≠ 0 := by
  let n := R.natDegree
  have hncastF : (n : IRSProfile.Field) ≠ 0 :=
    irsField_natCast_ne_zero_of_pos_le_eleven hpos hle
  have hncast : (n : Polynomial (Polynomial IRSProfile.Field)) ≠ 0 := by
    simpa only [← Polynomial.C_eq_natCast] using
      (Polynomial.C_ne_zero.mpr (Polynomial.C_ne_zero.mpr hncastF))
  have hlead : R.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hpos)
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hpos
  have hcoeff : R.derivative.coeff (n - 1) ≠ 0 := by
    rw [Polynomial.coeff_derivative]
    norm_cast
    have hm := mul_ne_zero hlead hncast
    change R.coeff n * (n : Polynomial (Polynomial IRSProfile.Field)) ≠ 0 at hm
    simpa only [hindex] using hm
  intro hzero
  exact hcoeff (by rw [hzero, Polynomial.coeff_zero])

theorem natDegree_derivative_eq_sub_one_of_pos_le_eleven
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hpos : 0 < R.natDegree) (hle : R.natDegree ≤ 11) :
    R.derivative.natDegree = R.natDegree - 1 := by
  apply le_antisymm (Polynomial.natDegree_derivative_le R)
  apply Polynomial.le_natDegree_of_ne_zero
  let n := R.natDegree
  have hncastF : (n : IRSProfile.Field) ≠ 0 :=
    irsField_natCast_ne_zero_of_pos_le_eleven hpos hle
  have hncast : (n : Polynomial (Polynomial IRSProfile.Field)) ≠ 0 := by
    simpa only [← Polynomial.C_eq_natCast] using
      (Polynomial.C_ne_zero.mpr (Polynomial.C_ne_zero.mpr hncastF))
  have hlead : R.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hpos)
  rw [Polynomial.coeff_derivative]
  norm_cast
  have hm := mul_ne_zero hlead hncast
  change R.coeff n * (n : Polynomial (Polynomial IRSProfile.Field)) ≠ 0 at hm
  simpa only [Nat.sub_add_cancel hpos] using hm

/-- Therefore the fixed-size derivative resultant used by sequential selection
is nonzero; fixed size agrees with the ordinary resultant because the
derivative has degree exactly `deg R - 1`. -/
theorem derivativeResultant_ne_zero
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hle : R.natDegree ≤ 11) :
    SequentialFactorSelection.derivativeResultant R ≠ 0 := by
  let A := Polynomial (Polynomial IRSProfile.Field)
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hirrMap : Irreducible (R.map φ) := by
    have hprimitive := hirr.isPrimitive (Nat.ne_of_gt hpos)
    exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hRmapDegree : (R.map φ).natDegree = R.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ R
  have hderivMapDegree : (R.map φ).derivative.natDegree = R.natDegree - 1 := by
    rw [Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective hφ]
    exact natDegree_derivative_eq_sub_one_of_pos_le_eleven R hpos hle
  have hderivMapNe : (R.map φ).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    intro hz
    exact derivative_ne_zero_of_pos_le_eleven R hpos hle
      (Polynomial.map_injective φ hφ (by simpa using hz))
  have hcoprime : IsCoprime (R.map φ) (R.map φ).derivative := by
    apply hirrMap.coprime_iff_not_dvd.mpr
    apply Polynomial.not_dvd_of_natDegree_lt hderivMapNe
    rw [hderivMapDegree, hRmapDegree]
    omega
  have hresMap := Polynomial.resultant_ne_zero
    (R.map φ) (R.map φ).derivative hcoprime
  intro hzero
  apply hresMap
  change Polynomial.resultant (R.map φ) (R.map φ).derivative
    (R.map φ).natDegree (R.map φ).derivative.natDegree = 0
  rw [hRmapDegree, hderivMapDegree, Polynomial.derivative_map,
    Polynomial.resultant_map_map]
  change φ (SequentialFactorSelection.derivativeResultant R) = 0
  rw [hzero, map_zero]

/-- A determinant of `N` polynomial entries, each of degree at most `D`, has
degree at most `N*D`. -/
theorem natDegree_det_le_card_mul
    {A : Type*} [CommRing A] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial A))
    (hentry : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ N * D := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) •
        (∏ i : Fin N, M (σ i) i)).natDegree ≤
          (∏ i : Fin N, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  refine hsign.trans ((Polynomial.natDegree_prod_le
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => M (σ i) i)).trans ?_)
  calc
    ∑ i ∈ (Finset.univ : Finset (Fin N)), (M (σ i) i).natDegree
        ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)), D :=
          Finset.sum_le_sum fun i hi => hentry (σ i) i
    _ = N * D := by simp

/-- Sylvester-resultant degree bound when every coefficient of both inputs has
coefficient-variable degree at most `D`. -/
theorem natDegree_resultant_le
    {A : Type*} [CommRing A]
    (f g : Polynomial (Polynomial A)) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (Polynomial.resultant f g m n).natDegree ≤ (m + n) * D := by
  unfold Polynomial.resultant
  apply natDegree_det_le_card_mul
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro jl
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · simp
  · intro jr
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · simp

/-- The derivative does not increase the `X`-degree of coefficients. -/
theorem derivative_coeff_natDegree_le
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    {D : ℕ} (hcoeff : ∀ i, (R.coeff i).natDegree ≤ D) (i : ℕ) :
    (R.derivative.coeff i).natDegree ≤ D := by
  rw [Polynomial.coeff_derivative]
  have hcast : (i + 1 : Polynomial (Polynomial IRSProfile.Field)).natDegree = 0 := by
    simpa only [map_add, map_one, Polynomial.C_eq_natCast] using
      (Polynomial.natDegree_C
        ((i : Polynomial IRSProfile.Field) + 1))
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add (hcoeff (i + 1)) (Nat.le_of_eq hcast)).trans (by omega))

/-- The fixed derivative resultant of a Cap72 factor has `X`-degree at most
`21 * 1760955 = 36980055`. -/
theorem derivativeResultant_natDegree_le
    {domain : IRSProfile.Index → IRSProfile.Field}
    {u v : IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant domain u v)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) :
    (SequentialFactorSelection.derivativeResultant R).natDegree ≤ 36980055 := by
  have hcoeff : ∀ i, (R.coeff i).natDegree ≤ 1760955 :=
    factor_coeff_natDegree_le Q hR hR0
  have hraw := natDegree_resultant_le
    (A := Polynomial IRSProfile.Field) R R.derivative
    R.natDegree (R.natDegree - 1) 1760955 hcoeff
    (derivative_coeff_natDegree_le R hcoeff)
  refine hraw.trans ?_
  have hn := factor_natDegree_le_eleven Q hR
  norm_num [SequentialFactorSelection.derivativeResultant] at *
  omega

/-- The leading `Y` coefficient has `X`-degree at most the same Cap72 bound. -/
theorem leadingCoeff_natDegree_le
    {domain : IRSProfile.Index → IRSProfile.Field}
    {u v : IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant domain u v)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) :
    R.leadingCoeff.natDegree ≤ 1760955 := by
  change (R.coeff R.natDegree).natDegree ≤ 1760955
  exact factor_coeff_natDegree_le Q hR hR0 R.natDegree

/-- The concrete field is vastly larger than both exceptional-degree budgets. -/
theorem cap72_exceptional_degree_lt_field_card :
    1760955 + 36980055 < Fintype.card IRSProfile.Field := by
  norm_num [IRSProfile.Field, KoalaBear.card_ext6, KoalaBear.fieldSize]

/-- Fully concrete specialization witness for an irreducible positive-`Y`
normalized Cap72 factor. -/
theorem exists_good_specialization_cap72
    {domain : IRSProfile.Index → IRSProfile.Field}
    {u v : IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant domain u v)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hRmem : R ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial)
    (hpositive : 0 < R.natDegree) :
    ∃ x₀ ∈ (Finset.univ : Finset IRSProfile.Field),
      (SequentialFactorSelection.specializeX x₀ R).natDegree = R.natDegree ∧
      (SequentialFactorSelection.derivativeResultant R).eval
        (Polynomial.C x₀) ≠ 0 := by
  have hRdvd : R ∣ Q.polynomial :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRmem
  have hR0 : R ≠ 0 := by
    intro hzero
    subst R
    exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q.polynomial hRmem
  have hdegree := factor_natDegree_le_eleven Q hRdvd
  have hirr : Irreducible R :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor R hRmem
  apply SequentialFactorSelection.exists_good_specialization R hR0
    (derivativeResultant_ne_zero R hirr hpositive hdegree)
      (Finset.univ : Finset IRSProfile.Field)
  have hlead := leadingCoeff_natDegree_le Q R hRdvd hR0
  have hres := derivativeResultant_natDegree_le Q R hRdvd hR0
  have hcard := cap72_exceptional_degree_lt_field_card
  simpa using lt_of_le_of_lt (Nat.add_le_add hlead hres) hcard

end

end ProximityPrize.SubmissionLower.Cap72FactorAudit
