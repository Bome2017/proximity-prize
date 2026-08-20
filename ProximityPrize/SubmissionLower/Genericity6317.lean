/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Grading6317

/-!
# Honest generic middle-coordinate specialization

For every irreducible positive-`Y` factor `R` we choose a middle-coordinate value `x₀` at
which both its leading coefficient and its `Y`-resultant with its derivative remain nonzero.
The excluded set is bounded by a concrete polynomial of degree at most
`2 * natDegreeY R * degreeX R`.  This is deliberately proved here rather than hidden behind a
genericity assumption.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate ToRatFunc
open scoped BigOperators

namespace Genericity6317

variable {F : Type} [Field F]

/-- Specialize the middle variable `X`, leaving a polynomial in `F[Z][Y]`. -/
noncomputable def specializeX (x : F) (R : F[X][X][Y]) : F[X][Y] :=
  Bivariate.evalX (Polynomial.C x) R

theorem specializeX_eq_map (x : F) (R : F[X][X][Y]) :
    specializeX x R = R.map (Polynomial.evalRingHom (Polynomial.C x)) := by
  simp [specializeX, Bivariate.evalX_eq_map]

/-! ## A local copy of the needed Sylvester degree estimate -/

private theorem resultant_natDegree_le {K : Type} [Field K]
    (A B : K[X][Y]) (m n : ℕ) :
    (Polynomial.resultant B A n m).natDegree ≤
      m * Bivariate.degreeX B + n * Bivariate.degreeX A := by
  classical
  let M : Matrix (Fin (n + m)) (Fin (n + m)) K[X] := Polynomial.sylvester B A n m
  have hcoeff (P : K[X][Y]) (k : ℕ) :
      (P.coeff k).natDegree ≤ Bivariate.degreeX P :=
    Bivariate.coeff_natDegree_le_degreeX P k
  let bound : Fin (n + m) → ℕ :=
    Fin.addCases (fun _ : Fin n ⇒ Bivariate.degreeX A)
      (fun _ : Fin m ⇒ Bivariate.degreeX B)
  have hentry (σ : Equiv.Perm (Fin (n + m))) (i : Fin (n + m)) :
      (M (σ i) i).natDegree ≤ bound i := by
    cases i using Fin.addCases with
    | left i₀ =>
        simp only [bound, Fin.addCases_left]
        have hM : M (σ (.castAdd m i₀)) (.castAdd m i₀) =
            if ((σ (.castAdd m i₀) : ℕ) ∈ Set.Icc (i₀ : ℕ) ((i₀ : ℕ) + m))
            then A.coeff ((σ (.castAdd m i₀) : ℕ) - i₀) else 0 := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        by_cases h : (σ (.castAdd m i₀) : ℕ) ∈ Set.Icc (i₀ : ℕ) ((i₀ : ℕ) + m)
        · simp only [hM, h, if_pos]; exact hcoeff A _
        · simp [hM, h]
    | right i₀ =>
        simp only [bound, Fin.addCases_right]
        have hM : M (σ (.natAdd n i₀)) (.natAdd n i₀) =
            if ((σ (.natAdd n i₀) : ℕ) ∈ Set.Icc (i₀ : ℕ) ((i₀ : ℕ) + n))
            then B.coeff ((σ (.natAdd n i₀) : ℕ) - i₀) else 0 := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        by_cases h : (σ (.natAdd n i₀) : ℕ) ∈ Set.Icc (i₀ : ℕ) ((i₀ : ℕ) + n)
        · simp only [hM, h, if_pos]; exact hcoeff B _
        · simp [hM, h]
  have hterm (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree ≤
        m * Bivariate.degreeX B + n * Bivariate.degreeX A := by
    refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ ⇒ hentry σ i).trans_eq ?_
    simp [bound, Fin.sum_univ_add, Nat.add_comm]
  have hdet : M.det.natDegree ≤
      m * Bivariate.degreeX B + n * Bivariate.degreeX A := by
    rw [Matrix.det_apply]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ ⇒ hterm σ)
  simpa [Polynomial.resultant, M, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdet

/-! ## Separability of a small-degree irreducible factor -/

theorem derivative_coeff_pred_ne_zero
    {A : Type} [CommRing A] [IsDomain A]
    (R : A[X]) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : A) ≠ 0) :
    R.derivative.coeff (R.natDegree - 1) ≠ 0 := by
  have hs : R.natDegree - 1 + 1 = R.natDegree := Nat.sub_add_cancel hpos
  rw [Polynomial.coeff_derivative, hs]
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
    (Polynomial.ne_zero_of_natDegree_gt hpos)) hcast

theorem derivative_ne_zero_of_natCast
    {A : Type} [CommRing A] [IsDomain A]
    (R : A[X]) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : A) ≠ 0) : R.derivative ≠ 0 := by
  intro hzero
  exact derivative_coeff_pred_ne_zero R hpos hcast (by simp [hzero])

theorem derivative_natDegree_eq_pred
    {A : Type} [CommRing A] [IsDomain A]
    (R : A[X]) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : A) ≠ 0) :
    R.derivative.natDegree = R.natDegree - 1 := by
  apply le_antisymm (Polynomial.natDegree_derivative_le R)
  exact Polynomial.le_natDegree_of_ne_zero
    (derivative_coeff_pred_ne_zero R hpos hcast)

theorem derivative_degreeX_le (R : F[X][Y]) :
    Bivariate.degreeX R.derivative ≤ Bivariate.degreeX R := by
  classical
  unfold Bivariate.degreeX
  refine Finset.sup_le ?_
  intro i hi
  rw [Polynomial.coeff_derivative]
  calc
    (R.coeff (i + 1) * (i + 1 : F[X])).natDegree ≤
        (R.coeff (i + 1)).natDegree + ((i + 1 : F[X])).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (R.coeff (i + 1)).natDegree := by
      rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C, Nat.add_zero]
    _ ≤ R.support.sup (fun j ⇒ (R.coeff j).natDegree) :=
      Bivariate.coeff_natDegree_le_degreeX R (i + 1)

theorem isCoprime_derivative_of_irreducible
    {A : Type} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    {R : A[X]} (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : A) ≠ 0) : IsCoprime R R.derivative := by
  refine hirr.coprime_iff_not_dvd.mpr ?_
  intro hdvd
  have hderiv := derivative_ne_zero_of_natCast R hpos hcast
  have hle := Polynomial.natDegree_le_of_dvd hdvd hderiv
  have hlt := Polynomial.natDegree_derivative_lt (by omega : R.natDegree ≠ 0)
  omega

/-- The product whose nonvanishing preserves both degree and separability. -/
noncomputable def genericityWitness (R : F[X][X][Y]) : F[X][X] :=
  R.leadingCoeff *
    Polynomial.resultant R R.derivative R.natDegree (R.natDegree - 1)

theorem genericityWitness_ne_zero
    {R : F[X][X][Y]} (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : F) ≠ 0) : genericityWitness R ≠ 0 := by
  have hcast' : (R.natDegree : F[X][X]) ≠ 0 := by
    simpa [← Polynomial.C_eq_natCast] using
      (Polynomial.C_ne_zero.mpr (Polynomial.C_ne_zero.mpr hcast))
  have hcop := isCoprime_derivative_of_irreducible hirr hpos hcast'
  have hres : Polynomial.resultant R R.derivative R.natDegree
      (R.natDegree - 1) ≠ 0 := by
    have hdefault := Polynomial.resultant_ne_zero R R.derivative hcop
    simpa [derivative_natDegree_eq_pred R hpos hcast'] using hdefault
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero) hres

theorem genericityWitness_natDegree_le
    {R : F[X][X][Y]} (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : F) ≠ 0) :
    (genericityWitness R).natDegree ≤
      2 * R.natDegree * Bivariate.degreeX R := by
  have hcast' : (R.natDegree : F[X][X]) ≠ 0 := by
    simpa [← Polynomial.C_eq_natCast] using
      (Polynomial.C_ne_zero.mpr (Polynomial.C_ne_zero.mpr hcast))
  have hderivDegree := derivative_natDegree_eq_pred R hpos hcast'
  have hres := resultant_natDegree_le
    (K := F[X]) R.derivative R (R.natDegree - 1) R.natDegree
  have hlc : R.leadingCoeff.natDegree ≤ Bivariate.degreeX R := by
    exact Bivariate.coeff_natDegree_le_degreeX R R.natDegree
  calc
    (genericityWitness R).natDegree ≤ R.leadingCoeff.natDegree +
        (Polynomial.resultant R R.derivative R.natDegree
          (R.natDegree - 1)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ Bivariate.degreeX R +
        ((R.natDegree - 1) * Bivariate.degreeX R +
          R.natDegree * Bivariate.degreeX R.derivative) :=
      Nat.add_le_add hlc hres
    _ ≤ Bivariate.degreeX R +
        ((R.natDegree - 1) * Bivariate.degreeX R +
          R.natDegree * Bivariate.degreeX R) := by
      exact Nat.add_le_add_left
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left R.natDegree (derivative_degreeX_le R)) _) _
    _ = 2 * R.natDegree * Bivariate.degreeX R := by
      rw [← Nat.add_mul, Nat.add_assoc, Nat.sub_add_cancel hpos]
      ring

/-! ## Counting and choosing an admissible point -/

noncomputable def genericityBadSet (R : F[X][X][Y]) : Finset F :=
  Finset.univ.filter fun x ⇒ (genericityWitness R).eval (Polynomial.C x) = 0

theorem genericityBadSet_card_le
    {R : F[X][X][Y]} (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hcast : (R.natDegree : F) ≠ 0) :
    (genericityBadSet R).card ≤ 2 * R.natDegree * Bivariate.degreeX R := by
  classical
  let p := genericityWitness R
  have hp : p ≠ 0 := genericityWitness_ne_zero hirr hpos hcast
  have hset : genericityBadSet R =
      Finset.univ.filter (fun x ⇒ Bivariate.evalX x (Bivariate.swap p) = 0) := by
    ext x
    simp only [genericityBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Bivariate.evalY_eq_evalX_swap]
    rfl
  rw [hset]
  refine (Bivariate.card_evalX_eq_zero_le_degreeX (Bivariate.swap p)
    (Bivariate.swap (R := F)).injective.ne hp Finset.univ).trans ?_
  rw [Bivariate.degreeX_swap]
  exact genericityWitness_natDegree_le hpos hcast

theorem target_natCast_ne_zero {d : ℕ} (hpos : 0 < d) (hle : d ≤ targetDY) :
    (d : IRSProfile.Field) ≠ 0 := by
  intro hzero
  have hdlt : d < KoalaBear.fieldSize := by
    norm_num [targetDY, KoalaBear.fieldSize] at hle ⊢
    omega
  have h0lt : 0 < KoalaBear.fieldSize := by norm_num [KoalaBear.fieldSize]
  have heq := CharP.natCast_injOn_Iio IRSProfile.Field KoalaBear.fieldSize
    hdlt h0lt hzero
  omega

/-- The concrete field is much larger than the complete genericity exclusion for one factor. -/
theorem exists_target_generic_point
    {R : IRSProfile.Field[X][X][Y]}
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hdegreeY : R.natDegree ≤ targetDY)
    (hdegreeX : Bivariate.degreeX R ≤ targetDX) :
    ∃ x₀ : IRSProfile.Field, x₀ ∉ genericityBadSet R := by
  classical
  have hcast := target_natCast_ne_zero hpos hdegreeY
  have hbad := genericityBadSet_card_le hirr hpos hcast
  have hnumeric : 2 * R.natDegree * Bivariate.degreeX R <
      Fintype.card IRSProfile.Field := by
    calc
      2 * R.natDegree * Bivariate.degreeX R ≤ 2 * targetDY * targetDX := by
        exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl hdegreeY) hdegreeX
      _ < Fintype.card IRSProfile.Field := by
        norm_num [targetDY, targetDX, IRSProfile.Field, KoalaBear.Ext6]
  have hcard : (genericityBadSet R).card < (Finset.univ : Finset IRSProfile.Field).card := by
    simpa using hbad.trans_lt hnumeric
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨x₀, hx₀⟩

theorem generic_point_properties
    {R : IRSProfile.Field[X][X][Y]}
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hdegreeY : R.natDegree ≤ targetDY)
    {x₀ : IRSProfile.Field} (hx₀ : x₀ ∉ genericityBadSet R) :
    (specializeX x₀ R).natDegree = R.natDegree ∧
      ((specializeX x₀ R).map (univPolyHom (F := IRSProfile.Field))).Separable := by
  classical
  have hcast := target_natCast_ne_zero hpos hdegreeY
  have hwitness : (genericityWitness R).eval (Polynomial.C x₀) ≠ 0 := by
    simpa [genericityBadSet] using hx₀
  have hlead : R.leadingCoeff.eval (Polynomial.C x₀) ≠ 0 := by
    intro hz
    apply hwitness
    simp [genericityWitness, hz]
  have hres :
      (Polynomial.resultant R R.derivative R.natDegree
        (R.natDegree - 1)).eval (Polynomial.C x₀) ≠ 0 := by
    intro hz
    apply hwitness
    simp [genericityWitness, hz]
  let ev : IRSProfile.Field[X][X] →+* IRSProfile.Field[X] :=
    Polynomial.evalRingHom (Polynomial.C x₀)
  let S : IRSProfile.Field[X][Y] := specializeX x₀ R
  have hSmap : S = R.map ev := by
    simp [S, ev, specializeX_eq_map]
  have hSdegree : S.natDegree = R.natDegree := by
    rw [hSmap]
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero ev hlead
  have hcastZ : (R.natDegree : IRSProfile.Field[X]) ≠ 0 := by
    simpa [← Polynomial.C_eq_natCast] using Polynomial.C_ne_zero.mpr hcast
  have hSderivDegree : S.derivative.natDegree = R.natDegree - 1 := by
    rw [derivative_natDegree_eq_pred S (hSdegree.symm ▸ hpos)]
    simpa [hSdegree] using hcastZ
  have hresS : Polynomial.resultant S S.derivative R.natDegree
      (R.natDegree - 1) ≠ 0 := by
    rw [hSmap, Polynomial.derivative_map]
    simpa [ev, Polynomial.resultant_map_map] using hres
  let φ := univPolyHom (F := IRSProfile.Field)
  let T : (RatFunc IRSProfile.Field)[X] := S.map φ
  have hTdegree : T.natDegree = R.natDegree := by
    rw [T, Polynomial.natDegree_map_eq_of_injective
      (RationalFunctions.univPolyHom_injective (F := IRSProfile.Field)), hSdegree]
  have hTderivDegree : T.derivative.natDegree = R.natDegree - 1 := by
    rw [T, Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective
        (RationalFunctions.univPolyHom_injective (F := IRSProfile.Field)), hSderivDegree]
  have hresT : Polynomial.resultant T T.derivative R.natDegree
      (R.natDegree - 1) ≠ 0 := by
    intro hz
    apply hresS
    apply RationalFunctions.univPolyHom_injective (F := IRSProfile.Field)
    rw [Polynomial.resultant_map_map]
    simpa [T, Polynomial.derivative_map] using hz
  have hdefault : Polynomial.resultant T T.derivative ≠ 0 := by
    simpa [hTdegree, hTderivDegree] using hresT
  have hsep : T.Separable := by
    by_contra hn
    apply hdefault
    exact Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (by intro hz; simpa [hz] using hTdegree.trans hpos.ne'), hn⟩
  exact ⟨hSdegree, hsep⟩

/-- A fully packaged admissible middle-coordinate value for a target factor. -/
theorem exists_target_specialization
    {R : IRSProfile.Field[X][X][Y]}
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hdegreeY : R.natDegree ≤ targetDY)
    (hdegreeX : Bivariate.degreeX R ≤ targetDX) :
    ∃ x₀ : IRSProfile.Field,
      (specializeX x₀ R).natDegree = R.natDegree ∧
      ((specializeX x₀ R).map
        (univPolyHom (F := IRSProfile.Field))).Separable := by
  obtain ⟨x₀, hx₀⟩ := exists_target_generic_point hirr hpos hdegreeY hdegreeX
  exact ⟨x₀, generic_point_properties hirr hpos hdegreeY hx₀⟩

end Genericity6317
end ProximityPrize.SubmissionLower
