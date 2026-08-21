import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators
import ProximityPrize.SubmissionLower.BCHKSSeparableFactors
import ProximityPrize.SubmissionLower.BCHKSPartialSpecializationFunctor

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions ToRatFunc Ideal
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace RawHenselDegree

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Evaluation of a polynomial in the original root coordinate
`Y = T / leadingCoeff(H)`. -/
noncomputable def rawLiftHom : F[X][Y] →+* 𝕃 H :=
  Polynomial.eval₂RingHom (liftToFunctionField (H := H))
    (initialValue (H := H))

@[simp] theorem rawLiftHom_apply (P : F[X][Y]) :
    rawLiftHom (H := H) P =
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) P := rfl

private theorem mk_monicizeRatFunc_eq_W_pow_mul_rawLift :
    (Ideal.Quotient.mk (Ideal.span ({monicizeRatFunc H} : Set (Polynomial (RatFunc F))))
        (monicizeRatFunc H) : 𝕃 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) *
        rawLiftHom (H := H) H := by
  unfold rawLiftHom initialValue liftToFunctionField functionFieldT coeffAsRatFunc
  unfold monicizeRatFunc
  simp only [Polynomial.coeff_natDegree, ToRatFunc.bivPolyHom,
    Polynomial.coe_mapRingHom, Polynomial.map_C, RingHom.comp_apply]
  let Wp : Polynomial (RatFunc F) :=
    Polynomial.C (univPolyHom (F := F) H.leadingCoeff)
  let I : Ideal (Polynomial (RatFunc F)) := Ideal.span
    ({Wp ^ (H.natDegree - 1) *
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
        (Polynomial.X / Wp) H} : Set (Polynomial (RatFunc F)))
  let q : Polynomial (RatFunc F) →+* 𝕃 H := Ideal.Quotient.mk I
  have hW_ne : univPolyHom (F := F) H.leadingCoeff ≠ 0 := by
    intro h
    exact (Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt (Fact.out : 0 < H.natDegree)))
        (univPolyHom_injective (F := F) (by simpa using h))
  have hdiv : q (Polynomial.X / Wp) = q Polynomial.X / q Wp := by
    dsimp [Wp]
    rw [Polynomial.div_C, map_mul, div_eq_mul_inv]
    congr 1
    have hmul : q (Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) *
        q (Polynomial.C ((univPolyHom (F := F) H.leadingCoeff)⁻¹)) = 1 := by
      rw [← map_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hW_ne]
      exact map_one q
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  change q
      (Wp ^ (H.natDegree - 1) *
        Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
          (Polynomial.X / Wp) H) =
    q Wp ^ (H.natDegree - 1) *
      Polynomial.eval₂
        (q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C))
        (q Polynomial.X / q Wp) H
  rw [map_mul, map_pow, ← hdiv, Polynomial.hom_eval₂]
  have hhom : q.comp
      (RingHom.comp Polynomial.C (univPolyHom (F := F)) :
        F[X] →+* Polynomial (RatFunc F)) =
      q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C) := by
    ext p <;> simp [RingHom.comp_apply]
  rw [hhom]

theorem rawLiftHom_H_eq_zero : rawLiftHom (H := H) H = 0 := by
  have hzero :
      (Ideal.Quotient.mk (Ideal.span ({monicizeRatFunc H} : Set (Polynomial (RatFunc F))))
        (monicizeRatFunc H) : 𝕃 H) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [mk_monicizeRatFunc_eq_W_pow_mul_rawLift] at hzero
  have hW : liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) ≠ 0 :=
    pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  exact (mul_eq_zero.mp hzero).resolve_left hW

/-- A function-field element with a polynomial representative of controlled
raw `Y`- and `Z`-degrees. -/
def RawBidegreeLe (a : 𝕃 H) (dY dZ : Nat) : Prop :=
  ∃ P : F[X][Y], rawLiftHom (H := H) P = a ∧
    P.natDegree ≤ dY ∧ degreeX P ≤ dZ

theorem RawBidegreeLe.zero (dY dZ : Nat) :
    RawBidegreeLe (H := H) 0 dY dZ := by
  exact ⟨0, by simp [rawLiftHom], by simp, by simp [degreeX]⟩

theorem RawBidegreeLe.one : RawBidegreeLe (H := H) 1 0 0 := by
  refine ⟨1, by simp [rawLiftHom], by simp, ?_⟩
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  cases i with
  | zero => simp
  | succ i =>
      have hz : (1 : F[X][Y]).coeff (i + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simp)
      exact ((Polynomial.mem_support_iff.mp hi) hz).elim

theorem RawBidegreeLe.neg {a : 𝕃 H} {dY dZ : Nat}
    (ha : RawBidegreeLe (H := H) a dY dZ) :
    RawBidegreeLe (H := H) (-a) dY dZ := by
  obtain ⟨P, hP, hPY, hPZ⟩ := ha
  refine ⟨-P, by simpa [rawLiftHom] using congrArg Neg.neg hP, ?_, ?_⟩
  · simpa using hPY
  · simpa [degreeX] using hPZ

private theorem degreeX_add_le (P Q : F[X][Y]) :
    degreeX (P + Q) ≤ max (degreeX P) (degreeX Q) := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  have hcoeff : (P + Q).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  rw [Polynomial.coeff_add] at hcoeff ⊢
  calc
    (P.coeff i + Q.coeff i).natDegree ≤
        max (P.coeff i).natDegree (Q.coeff i).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ max (degreeX P) (degreeX Q) := by
      apply max_le
      · by_cases hPi : P.coeff i = 0
        · simp [hPi]
        · exact (coeff_natDegree_le_degreeX P i).trans (Nat.le_max_left _ _)
      · by_cases hQi : Q.coeff i = 0
        · simp [hQi]
        · exact (coeff_natDegree_le_degreeX Q i).trans (Nat.le_max_right _ _)

theorem RawBidegreeLe.add {a b : 𝕃 H} {aY aZ bY bZ : Nat}
    (ha : RawBidegreeLe (H := H) a aY aZ)
    (hb : RawBidegreeLe (H := H) b bY bZ) :
    RawBidegreeLe (H := H) (a + b) (max aY bY) (max aZ bZ) := by
  obtain ⟨P, hP, hPY, hPZ⟩ := ha
  obtain ⟨Q, hQ, hQY, hQZ⟩ := hb
  refine ⟨P + Q, ?_, ?_, ?_⟩
  · change rawLiftHom (H := H) (P + Q) = a + b
    rw [map_add, hP, hQ]
  · exact (Polynomial.natDegree_add_le P Q).trans (max_le_max hPY hQY)
  · exact (degreeX_add_le P Q).trans (max_le_max hPZ hQZ)

theorem RawBidegreeLe.mul {a b : 𝕃 H} {aY aZ bY bZ : Nat}
    (ha : RawBidegreeLe (H := H) a aY aZ)
    (hb : RawBidegreeLe (H := H) b bY bZ) :
    RawBidegreeLe (H := H) (a * b) (aY + bY) (aZ + bZ) := by
  obtain ⟨P, hP, hPY, hPZ⟩ := ha
  obtain ⟨Q, hQ, hQY, hQZ⟩ := hb
  refine ⟨P * Q, ?_, ?_, ?_⟩
  · change rawLiftHom (H := H) (P * Q) = a * b
    rw [map_mul, hP, hQ]
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hPY hQY)
  · exact (degreeX_mul_le P Q).trans (Nat.add_le_add hPZ hQZ)

theorem RawBidegreeLe.pow {a : 𝕃 H} {aY aZ : Nat}
    (ha : RawBidegreeLe (H := H) a aY aZ) (n : Nat) :
    RawBidegreeLe (H := H) (a ^ n) (n * aY) (n * aZ) := by
  induction n with
  | zero => simpa using (RawBidegreeLe.one (H := H))
  | succ n ih =>
      simpa [pow_succ, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using ih.mul ha

theorem RawBidegreeLe.mono {a : 𝕃 H} {aY aZ bY bZ : Nat}
    (ha : RawBidegreeLe (H := H) a aY aZ)
    (hY : aY ≤ bY) (hZ : aZ ≤ bZ) :
    RawBidegreeLe (H := H) a bY bZ := by
  obtain ⟨P, hP, hPY, hPZ⟩ := ha
  exact ⟨P, hP, hPY.trans hY, hPZ.trans hZ⟩

theorem RawBidegreeLe.finsetSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → 𝕃 H)
    (dY dZ : Nat) (ha : ∀ i ∈ s, RawBidegreeLe (H := H) (a i) dY dZ) :
    RawBidegreeLe (H := H) (∑ i ∈ s, a i) dY dZ := by
  induction s using Finset.induction_on with
  | empty => simpa using RawBidegreeLe.zero (H := H) dY dZ
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply RawBidegreeLe.mono
        ((ha i (by simp)).add (ih (fun j hj => ha j (by simp [hj]))))
      · simp
      · simp

theorem RawBidegreeLe.finsetProd
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → 𝕃 H)
    (dY dZ : ι → Nat)
    (ha : ∀ i ∈ s, RawBidegreeLe (H := H) (a i) (dY i) (dZ i)) :
    RawBidegreeLe (H := H) (∏ i ∈ s, a i)
      (∑ i ∈ s, dY i) (∑ i ∈ s, dZ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using RawBidegreeLe.one (H := H)
  | @insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his, Finset.sum_insert his]
      exact (ha i (by simp)).mul (ih (fun j hj => ha j (by simp [hj])))

theorem RawBidegreeLe.liftCoeff (c : F[X]) :
    RawBidegreeLe (H := H) (liftToFunctionField (H := H) c) 0 c.natDegree := by
  refine ⟨Polynomial.C c, by simp [rawLiftHom], by simp, ?_⟩
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    cases i with
    | zero => rfl
    | succ i =>
        exfalso
        have hz : (Polynomial.C c : F[X][Y]).coeff (i + 1) = 0 := by simp
        exact (Polynomial.mem_support_iff.mp hi) hz
  subst i
  simp

theorem RawBidegreeLe.fieldConst (c : F) :
    RawBidegreeLe (H := H) (fieldTo𝕃 (H := H) c) 0 0 := by
  change RawBidegreeLe (H := H)
    (liftToFunctionField (H := H) (Polynomial.C c)) 0 0
  exact (RawBidegreeLe.liftCoeff (H := H) (Polynomial.C c)).mono
    (le_refl _) (by simp)

theorem RawBidegreeLe.commonZ :
    RawBidegreeLe (H := H)
      (liftToFunctionField (H := H) Polynomial.X) 0 1 := by
  exact (RawBidegreeLe.liftCoeff (H := H) Polynomial.X).mono
    (le_refl _) (by simp)

theorem RawBidegreeLe.initialValue :
    RawBidegreeLe (H := H) (initialValue (H := H)) 1 0 := by
  refine ⟨Polynomial.X, by simp [rawLiftHom], by simp, ?_⟩
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  simp only [Polynomial.coeff_X]
  split <;> simp

theorem shiftedCoeffPolynomial_eq_map_shift (x₀ : F) (p : F[X][X]) :
    shiftedCoeffPolynomial (H := H) x₀ p =
      (p.comp (Polynomial.C (Polynomial.C x₀) + Polynomial.X)).map
        (liftToFunctionField (H := H)) := by
  unfold shiftedCoeffPolynomial
  rw [ProximityPrize.SubmissionLower.FiniteHensel.shiftMap_apply]
  have hinner :
      (Polynomial.C (Polynomial.C x₀) + Polynomial.X).map
          (liftToFunctionField (H := H)) =
        Polynomial.C (fieldTo𝕃 (H := H) x₀) + Polynomial.X := by
    simp [fieldTo𝕃]
  rw [← hinner]
  rw [← Polynomial.map_comp]

theorem shifted_coeff_natDegree_le_degreeX
    (x₀ : F) (p : F[X][X]) (n : Nat) :
    ((p.comp (Polynomial.C (Polynomial.C x₀) + Polynomial.X)).coeff n).natDegree ≤
      degreeX p := by
  classical
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Polynomial.coeff_C_mul]
  have hinner :
      (Polynomial.C (Polynomial.C x₀) + Polynomial.X : F[X][X]) =
        (Polynomial.C x₀ + Polynomial.X).map (Polynomial.C : F →+* F[X]) := by
    simp
  rw [hinner, ← Polynomial.map_pow, Polynomial.coeff_map]
  calc
    (p.coeff i * Polynomial.C (((Polynomial.C x₀ + Polynomial.X) ^ i).coeff n)).natDegree ≤
        (p.coeff i).natDegree +
          (Polynomial.C (((Polynomial.C x₀ + Polynomial.X) ^ i).coeff n)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (p.coeff i).natDegree + 0 := by simp
    _ ≤ degreeX p := by
      simpa using coeff_natDegree_le_degreeX p i

theorem RawBidegreeLe.shiftedCoeff
    (x₀ : F) (p : F[X][X]) (n : Nat) :
    RawBidegreeLe (H := H) ((shiftedCoeffPolynomial (H := H) x₀ p).coeff n)
      0 (degreeX p) := by
  let c : F[X] := (p.comp
    (Polynomial.C (Polynomial.C x₀) + Polynomial.X)).coeff n
  have heq : (shiftedCoeffPolynomial (H := H) x₀ p).coeff n =
      liftToFunctionField (H := H) c := by
    rw [shiftedCoeffPolynomial_eq_map_shift]
    simp [c]
  rw [heq]
  exact (RawBidegreeLe.liftCoeff (H := H) c).mono (le_refl _)
    (shifted_coeff_natDegree_le_degreeX x₀ p n)

theorem RawBidegreeLe.zeta
    (x₀ : F) (R : F[X][X][Y]) (dY dZ : Nat)
    (hY : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ dY)
    (hZ : degreeX (Bivariate.evalX (Polynomial.C x₀) R.derivative) ≤ dZ) :
    RawBidegreeLe (H := H) (zeta R x₀ H) dY dZ := by
  exact ⟨Bivariate.evalX (Polynomial.C x₀) R.derivative, rfl, hY, hZ⟩

private theorem degreeX_le_totalDegree (P : F[X][Y]) :
    degreeX P ≤ Bivariate.totalDegree P := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  exact (Nat.le_add_right _ i).trans (Bivariate.coeff_totalDegree_le P hi)

theorem RawBidegreeLe.zeta_of_yzCap
    (x₀ : F) (R : F[X][X][Y]) (D : Nat)
    (hYZ : YZCap R D) :
    RawBidegreeLe (H := H)
      (RationalFunctions.HenselNumerators.zeta R x₀ H)
      (R.natDegree - 1) D := by
  apply RawBidegreeLe.zeta (H := H) x₀ R
  · rw [Bivariate.evalX_eq_map]
    exact Polynomial.natDegree_map_le.trans
      (Polynomial.natDegree_derivative_le R)
  · let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
    have hder : Bivariate.evalX (Polynomial.C x₀) R.derivative = P.derivative := by
      simp [P, Bivariate.evalX_eq_map, Polynomial.derivative_map]
    rw [hder]
    exact (degreeX_derivative_le P).trans
      ((degreeX_le_totalDegree P).trans (evalX_totalDegree_le_of_yzCap x₀ R hYZ))

theorem degreeX_coeff_le_of_yzCap
    (R : F[X][X][Y]) (D j : Nat)
    (hYZ : YZCap R D) : degreeX (R.coeff j) ≤ D := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro a ha
  have hne : (R.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
  exact (Nat.le_add_right _ j).trans (hYZ j a hne)

theorem RawBidegreeLe.shiftedCoeff_of_yzCap
    (x₀ : F) (R : F[X][X][Y]) (D j n : Nat)
    (hYZ : YZCap R D) :
    RawBidegreeLe (H := H)
      ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff n) 0 D := by
  exact (RawBidegreeLe.shiftedCoeff (H := H) x₀ (R.coeff j) n).mono
    (le_refl _) (degreeX_coeff_le_of_yzCap R D j hYZ)

/-- One cleared raw-Hensel residual term preserves the sharp bidegree
rectangle.  This is the central successor estimate. -/
theorem finiteHenselRawClearedTerm_bidegree
    (x₀ : F) (R : F[X][X][Y]) (D t j : Nat)
    (hYZ : YZCap R D) (hRpos : 0 < R.natDegree)
    (α : Nat → 𝕃 H)
    (hnum : ∀ i, i ≤ t →
      RawBidegreeLe (H := H)
        (α i * (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
          FiniteHenselWeight.denominatorExponent i)
        (FiniteHenselWeight.denominatorExponent i * (R.natDegree - 1) + 1)
        (FiniteHenselWeight.denominatorExponent i * D))
    (hj : j ∈ Finset.range (R.natDegree + 1)) :
    RawBidegreeLe (H := H)
      ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) *
          (FiniteHensel.truncSeries α t) ^ j).coeff (t + 1) *
        (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
          (FiniteHenselWeight.denominatorExponent (t + 1) - 1))
      (FiniteHenselWeight.denominatorExponent (t + 1) *
          (R.natDegree - 1) + 1)
      (FiniteHenselWeight.denominatorExponent (t + 1) * D) := by
  classical
  let ζ := RationalFunctions.HenselNumerators.zeta R x₀ H
  let e : Nat → Nat := FiniteHenselWeight.denominatorExponent
  have hζ : RawBidegreeLe (H := H) ζ (R.natDegree - 1) D :=
    RawBidegreeLe.zeta_of_yzCap (H := H) x₀ R D hYZ
  have hjle : j ≤ R.natDegree := by
    rw [Finset.mem_range] at hj
    omega
  rw [Polynomial.coeff_mul, Finset.sum_mul]
  apply RawBidegreeLe.finsetSum
  intro p hp
  rw [polynomial_coeff_pow]
  simp only [coeff_truncSeries_eq_if]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply RawBidegreeLe.finsetSum
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j, if l i ≤ t then α (l i) else 0) = 0 := by
      apply Finset.prod_eq_zero hi₀
      rw [if_neg (by omega)]
    rw [hz, mul_zero, zero_mul]
    exact RawBidegreeLe.zero _ _
  · push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    have hprod_if : (∏ i ∈ Finset.range j,
        if l i ≤ t then α (l i) else 0) =
        ∏ i ∈ Finset.range j, α (l i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_pos (hle i hi)]
    rw [hprod_if]
    let Pe := ∑ i ∈ Finset.range j, e (l i)
    let E := e (t + 1) - 1
    have hPe : Pe ≤ E := by
      let S1 := ∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)
      have h2b : 2 * p.2 = Pe + S1 := by
        dsimp [Pe, S1, e]
        rw [← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          by_cases hi : l i = 0
          · simp [FiniteHenselWeight.denominatorExponent, hi]
          · simp [FiniteHenselWeight.denominatorExponent, hi]
            omega
      have hbS1 : p.2 ≤ t * S1 := by
        rw [← hbsum]
        dsimp [S1]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        split
        · next h => rw [h]; simp
        · next h => rw [Nat.mul_one]; exact hle i hi
      have hE : E = 2 * t := by
        dsimp [E, e]
        rw [FiniteHenselWeight.denominatorExponent_succ]
        omega
      rw [hE]
      rcases Nat.lt_or_ge p.2 (t + 1) with hpt | hpt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h
          push Not at h
          interval_cases S1 <;> omega
        omega
    have hclearedProd : RawBidegreeLe (H := H)
        (∏ i ∈ Finset.range j,
          (α (l i) * ζ ^ e (l i)))
        (Pe * (R.natDegree - 1) + j) (Pe * D) := by
      have hp := RawBidegreeLe.finsetProd (H := H) (Finset.range j)
        (fun i => α (l i) * ζ ^ e (l i))
        (fun i => e (l i) * (R.natDegree - 1) + 1)
        (fun i => e (l i) * D)
        (fun i hi => by simpa [ζ, e] using hnum (l i) (hle i hi))
      apply hp.mono
      · dsimp [Pe]
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.card_range]
        rw [← Finset.sum_mul]
        simp
      · dsimp [Pe]
        rw [← Finset.sum_mul]
    have htail := hζ.pow (E - Pe)
    have hprodTail : RawBidegreeLe (H := H)
        ((∏ i ∈ Finset.range j, (α (l i) * ζ ^ e (l i))) * ζ ^ (E - Pe))
        (E * (R.natDegree - 1) + j) (E * D) := by
      apply (hclearedProd.mul htail).mono
      · have hsplit : Pe + (E - Pe) = E := Nat.add_sub_of_le hPe
        calc
          (Pe * (R.natDegree - 1) + j) +
              (E - Pe) * (R.natDegree - 1) =
            (Pe + (E - Pe)) * (R.natDegree - 1) + j := by ring
          _ ≤ E * (R.natDegree - 1) + j := by rw [hsplit]
      · have hsplit : Pe + (E - Pe) = E := Nat.add_sub_of_le hPe
        calc
          Pe * D + (E - Pe) * D = (Pe + (E - Pe)) * D := by ring
          _ ≤ E * D := by rw [hsplit]
    have hreassoc :
        (∏ i ∈ Finset.range j, α (l i)) * ζ ^ E =
          (∏ i ∈ Finset.range j, (α (l i) * ζ ^ e (l i))) * ζ ^ (E - Pe) := by
      calc
        (∏ i ∈ Finset.range j, α (l i)) * ζ ^ E =
            (∏ i ∈ Finset.range j, α (l i)) *
              (ζ ^ Pe * ζ ^ (E - Pe)) := by
          rw [← pow_add, Nat.add_sub_of_le hPe]
        _ = (∏ i ∈ Finset.range j, (α (l i) * ζ ^ e (l i))) *
              ζ ^ (E - Pe) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          change (∏ i ∈ Finset.range j, α (l i)) * (ζ ^ Pe * ζ ^ (E - Pe)) =
            ((∏ i ∈ Finset.range j, α (l i)) * ζ ^ Pe) * ζ ^ (E - Pe)
          ring
    have hcf := RawBidegreeLe.shiftedCoeff_of_yzCap (H := H)
      x₀ R D j p.1 hYZ
    have hterm : RawBidegreeLe (H := H)
        ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
          ((∏ i ∈ Finset.range j, α (l i)) * ζ ^ E))
        (E * (R.natDegree - 1) + j) ((E + 1) * D) := by
      rw [hreassoc]
      apply (hcf.mul hprodTail).mono
      · simp
      · exact Nat.le_of_eq (by ring)
    have heSucc : e (t + 1) = E + 1 := by
      dsimp [e, E]
      rw [FiniteHenselWeight.denominatorExponent_succ]
      omega
    have heSucc' : FiniteHenselWeight.denominatorExponent (t + 1) = E + 1 := by
      simpa [e] using heSucc
    have hterm' : RawBidegreeLe (H := H)
        ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j)).coeff p.1 *
          (∏ i ∈ Finset.range j, α (l i)) *
          (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
            (FiniteHenselWeight.denominatorExponent (t + 1) - 1))
        (E * (R.natDegree - 1) + j) ((E + 1) * D) := by
      simpa [ζ, E, mul_assoc] using hterm
    apply hterm'.mono
    · rw [heSucc']
      have hid : (E + 1) * (R.natDegree - 1) + 1 =
          E * (R.natDegree - 1) + R.natDegree := by
        obtain ⟨d, hd⟩ : ∃ d, R.natDegree = d + 1 :=
          ⟨R.natDegree - 1, by omega⟩
        rw [hd]
        rw [show d + 1 - 1 = d by omega]
        ring
      rw [hid]
      exact Nat.add_le_add_left hjle _
    · rw [heSucc']

/-- Sum of all raw residual terms at the successor coefficient. -/
theorem finiteHenselRawClearedResidual_bidegree
    (x₀ : F) (R : F[X][X][Y]) (D t : Nat)
    (hYZ : YZCap R D) (hRpos : 0 < R.natDegree)
    (α : Nat → 𝕃 H)
    (hnum : ∀ i, i ≤ t →
      RawBidegreeLe (H := H)
        (α i * (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
          FiniteHenselWeight.denominatorExponent i)
        (FiniteHenselWeight.denominatorExponent i * (R.natDegree - 1) + 1)
        (FiniteHenselWeight.denominatorExponent i * D)) :
    RawBidegreeLe (H := H)
      ((FiniteHensel.residual (liftedR (R := R) (H := H))
          (fieldTo𝕃 (H := H) x₀) α t).coeff (t + 1) *
        (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
          (FiniteHenselWeight.denominatorExponent (t + 1) - 1))
      (FiniteHenselWeight.denominatorExponent (t + 1) *
          (R.natDegree - 1) + 1)
      (FiniteHenselWeight.denominatorExponent (t + 1) * D) := by
  classical
  unfold FiniteHensel.residual
  rw [Polynomial.eval₂_eq_sum_range]
  have hcoeff :
      (∑ j ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
        FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀)
            ((liftedR (R := R) (H := H)).coeff j) *
          FiniteHensel.truncSeries α t ^ j).coeff (t + 1) =
        ∑ j ∈ Finset.range ((liftedR (R := R) (H := H)).natDegree + 1),
          (FiniteHensel.shiftMap (fieldTo𝕃 (H := H) x₀)
              ((liftedR (R := R) (H := H)).coeff j) *
            FiniteHensel.truncSeries α t ^ j).coeff (t + 1) := by simp
  rw [hcoeff, Finset.sum_mul]
  apply RawBidegreeLe.finsetSum
  intro j hjlift
  have hj : j ∈ Finset.range (R.natDegree + 1) := by
    rw [Finset.mem_range] at hjlift ⊢
    have hmap : (liftedR (R := R) (H := H)).natDegree ≤ R.natDegree :=
      Polynomial.natDegree_map_le
    omega
  have hcoeffmap : (liftedR (R := R) (H := H)).coeff j =
      (R.coeff j).map (liftToFunctionField (H := H)) := by
    simp [liftedR, Polynomial.coeff_map]
  rw [hcoeffmap]
  change RawBidegreeLe (H := H)
    ((shiftedCoeffPolynomial (H := H) x₀ (R.coeff j) *
        FiniteHensel.truncSeries α t ^ j).coeff (t + 1) *
      (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
        (FiniteHenselWeight.denominatorExponent (t + 1) - 1)) _ _
  exact finiteHenselRawClearedTerm_bidegree (H := H)
    x₀ R D t j hYZ hRpos α hnum hj

/-- Raw numerator of the finite Hensel coefficient, clearing only the actual
simple-root slope. -/
noncomputable def rawBetaField
    (x₀ : F) (R : F[X][X][Y]) (N t : Nat) : 𝕃 H :=
  finiteAlpha (R := R) (H := H) x₀ N t *
    (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
      FiniteHenselWeight.denominatorExponent t

/-- Strong-induction bidegree bound for every raw finite-Hensel numerator. -/
theorem rawBetaField_bidegree
    (x₀ : F) (R : F[X][X][Y]) (D : Nat)
    (hYZ : YZCap R D) (hRpos : 0 < R.natDegree)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (N : Nat) :
    ∀ t, t ≤ N →
      RawBidegreeLe (H := H) (rawBetaField (H := H) x₀ R N t)
        (FiniteHenselWeight.denominatorExponent t * (R.natDegree - 1) + 1)
        (FiniteHenselWeight.denominatorExponent t * D) := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          unfold rawBetaField finiteAlpha
          rw [FiniteHensel.liftCoeff_zero]
          simp only [FiniteHenselWeight.denominatorExponent_zero, pow_zero, mul_one,
            Nat.zero_mul, Nat.zero_add]
          exact RawBidegreeLe.initialValue (H := H)
      | succ m =>
          let oldp := FiniteHensel.liftPoly
            (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
              (initialValue (H := H)) N m
          let old : Nat → 𝕃 H := fun i => oldp.coeff i
          have hmN : m ≤ N := by omega
          have hdeg : oldp.natDegree ≤ m :=
            liftPoly_natDegree_le (R := R) (H := H) x₀ N m
          have hnum : ∀ i, i ≤ m →
              RawBidegreeLe (H := H)
                (old i * (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
                  FiniteHenselWeight.denominatorExponent i)
                (FiniteHenselWeight.denominatorExponent i * (R.natDegree - 1) + 1)
                (FiniteHenselWeight.denominatorExponent i * D) := by
            intro i hi
            have hdiag : old i = alphaDiagonal (R := R) (H := H) x₀ N i :=
              liftPoly_coeff_eq_diagonal (R := R) (H := H) x₀ N m i hi
            have hfinite : finiteAlpha (R := R) (H := H) x₀ N i =
                alphaDiagonal (R := R) (H := H) x₀ N i :=
              finiteAlpha_eq_alphaDiagonal (R := R) (H := H) x₀ N i (hi.trans hmN)
            rw [hdiag, ← hfinite]
            exact ih i (by omega) (hi.trans hmN)
          have hres := finiteHenselRawClearedResidual_bidegree (H := H)
            x₀ R D m hYZ hRpos old hnum
          have htruncN : FiniteHensel.truncSeries old N = oldp :=
            truncSeries_coeff_eq (H := H) oldp N (hdeg.trans hmN)
          have htruncm : FiniteHensel.truncSeries old m = oldp :=
            truncSeries_coeff_eq (H := H) oldp m hdeg
          have herr :
              (FiniteHensel.residual (liftedR (R := R) (H := H))
                (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) =
              (FiniteHensel.residual (liftedR (R := R) (H := H))
                (fieldTo𝕃 (H := H) x₀) old m).coeff (m + 1) := by
            unfold FiniteHensel.residual
            rw [htruncN, htruncm]
          have holdtop : old (m + 1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hnew : finiteAlpha (R := R) (H := H) x₀ N (m + 1) =
              -((FiniteHensel.residual (liftedR (R := R) (H := H))
                (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1)) /
                  RationalFunctions.HenselNumerators.zeta R x₀ H := by
            rw [finiteAlpha_eq_alphaDiagonal (R := R) (H := H) x₀ N (m + 1)
              (by omega)]
            unfold alphaDiagonal
            have hs := FiniteHensel.liftPoly_succ_coeff_sub
              (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
              (initialValue (H := H)) N m
            change (FiniteHensel.liftPoly
                (liftedR (R := R) (H := H)) (fieldTo𝕃 (H := H) x₀)
                (initialValue (H := H)) N (m + 1)).coeff (m + 1) -
              old (m + 1) = _ at hs
            rw [holdtop, sub_zero, ySlope_liftedR_eq_zeta] at hs
            exact hs
          rw [rawBetaField, hnew]
          have hepos : 0 < FiniteHenselWeight.denominatorExponent (m + 1) := by
            rw [FiniteHenselWeight.denominatorExponent_succ]
            omega
          have heq : FiniteHenselWeight.denominatorExponent (m + 1) =
              (FiniteHenselWeight.denominatorExponent (m + 1) - 1) + 1 := by omega
          rw [heq, pow_succ]
          have hreassoc :
              (-((FiniteHensel.residual (liftedR (R := R) (H := H))
                  (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1)) /
                    RationalFunctions.HenselNumerators.zeta R x₀ H) *
                ((RationalFunctions.HenselNumerators.zeta R x₀ H) ^
                    (FiniteHenselWeight.denominatorExponent (m + 1) - 1) *
                  RationalFunctions.HenselNumerators.zeta R x₀ H) =
              -((FiniteHensel.residual (liftedR (R := R) (H := H))
                  (fieldTo𝕃 (H := H) x₀) old N).coeff (m + 1) *
                (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
                  (FiniteHenselWeight.denominatorExponent (m + 1) - 1)) := by
            field_simp [hzeta]
          rw [hreassoc, herr]
          exact hres.neg

/-- Reduced base-`Z` gamma difference.  It clears only powers of the raw
simple-root slope; all monicization powers of `W` have disappeared. -/
noncomputable def rawBaseZGammaDifference
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y]) (N k : Nat) : 𝕃 H :=
  (evaluatedFiniteAlpha (R := R) (H := H) x₀ dx N k -
      (fieldTo𝕃 (H := H) u₀ +
        liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) u₁)) *
    (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
      FiniteHenselWeight.denominatorExponent k

/-- Bidegree bound for the reduced base-coordinate gamma numerator. -/
theorem rawBaseZGammaDifference_bidegree
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y]) (D N k : Nat)
    (hYZ : YZCap R D) (hRpos : 0 < R.natDegree)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (hkN : k ≤ N) :
    RawBidegreeLe (H := H)
      (rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k)
      (FiniteHenselWeight.denominatorExponent k * (R.natDegree - 1) + 1)
      (FiniteHenselWeight.denominatorExponent k * D + 1) := by
  let ζ := RationalFunctions.HenselNumerators.zeta R x₀ H
  let e : Nat → Nat := FiniteHenselWeight.denominatorExponent
  have hζ : RawBidegreeLe (H := H) ζ (R.natDegree - 1) D :=
    RawBidegreeLe.zeta_of_yzCap (H := H) x₀ R D hYZ
  have hsum : RawBidegreeLe (H := H)
      (evaluatedFiniteAlpha (R := R) (H := H) x₀ dx N k * ζ ^ e k)
      (e k * (R.natDegree - 1) + 1) (e k * D) := by
    unfold evaluatedFiniteAlpha
    rw [Finset.sum_mul]
    apply RawBidegreeLe.finsetSum
    intro i hi
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hiN : i ≤ N := hik.trans hkN
    have hβ := rawBetaField_bidegree (H := H) x₀ R D hYZ hRpos hzeta N i hiN
    have hei : e i ≤ e k := denominatorExponent_mono hik
    have hsplit : e k = e i + (e k - e i) := (Nat.add_sub_of_le hei).symm
    have htermEq :
        (finiteAlpha (R := R) (H := H) x₀ N i * fieldTo𝕃 (H := H) dx ^ i) *
            ζ ^ e k =
          (rawBetaField (H := H) x₀ R N i * fieldTo𝕃 (H := H) dx ^ i) *
            ζ ^ (e k - e i) := by
      have hpow : ζ ^ e k = ζ ^ e i * ζ ^ (e k - e i) := by
        rw [← pow_add, Nat.add_sub_of_le hei]
      rw [hpow]
      unfold rawBetaField
      ring
    rw [htermEq]
    have hdx := (RawBidegreeLe.fieldConst (H := H) dx).pow i
    have htail := hζ.pow (e k - e i)
    apply ((hβ.mul hdx).mul htail).mono
    · have heq : e i + (e k - e i) = e k := Nat.add_sub_of_le hei
      calc
        ((e i * (R.natDegree - 1) + 1) + i * 0) +
            (e k - e i) * (R.natDegree - 1) =
          (e i + (e k - e i)) * (R.natDegree - 1) + 1 := by ring
        _ ≤ e k * (R.natDegree - 1) + 1 := by rw [heq]
    · have heq : e i + (e k - e i) = e k := Nat.add_sub_of_le hei
      calc
        (e i * D + i * 0) + (e k - e i) * D =
            (e i + (e k - e i)) * D := by ring
        _ ≤ e k * D := by rw [heq]
  have haff : RawBidegreeLe (H := H)
      ((fieldTo𝕃 (H := H) u₀ +
          liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) u₁) *
        ζ ^ e k)
      (e k * (R.natDegree - 1)) (e k * D + 1) := by
    have hu0 := RawBidegreeLe.fieldConst (H := H) u₀
    have hu1 := RawBidegreeLe.fieldConst (H := H) u₁
    have hZ := RawBidegreeLe.commonZ (H := H)
    have hbase := hu0.add (hZ.mul hu1)
    apply (hbase.mul (hζ.pow (e k))).mono
    · simp
    · omega
  unfold rawBaseZGammaDifference
  rw [sub_mul]
  have hfinal := (hsum.add haff.neg).mono
    (max_le (le_refl _) (Nat.le_add_right _ 1))
    (max_le (Nat.le_add_right _ 1) (le_refl _))
  simpa [ζ, e, sub_eq_add_neg] using hfinal

/-- Raw polynomial representatives specialize by ordinary bivariate
evaluation whenever the original root coordinate is good. -/
theorem GoodAt.rawLiftHom
    {z y : F} {root : rationalRoot (monicize H) z}
    (P : F[X][Y])
    (hy : GoodAt z root (initialValue (H := H)) y) :
    GoodAt z root (rawLiftHom (H := H) P) (Polynomial.evalEval z y P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa [rawLiftHom, Polynomial.evalEval, Polynomial.eval_add] using
        GoodAt.add hP hQ
  | monomial n a =>
      have ha := GoodAt.liftToFunctionField (H := H) z root a
      have hp := GoodAt.mul ha (GoodAt.pow hy n)
      simpa [rawLiftHom, Polynomial.evalEval, Polynomial.eval_monomial,
        Polynomial.eval_mul] using hp

end RawHenselDegree
end ProximityPrize.SubmissionLower
