/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.CellAlgebra6317
import ProximityPrize.SubmissionLower.Capture6317

/-!
# The repaired BCHKS heavy-cell lemma

This file proves the two counting principles used by a heavy factor cell and packages the exact
nonmonic capture hypotheses.  The algebraic proof never evaluates an arbitrary function-field
element at a scalar.  It first proves a cleared identity in the regular quotient and then uses the
place-local map from `Place6317`.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators ENNReal NNReal

namespace RF6317
noncomputable section HeavyCell
namespace HeavyCell

open HenselNumerators Place CellAlgebra

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {R : F[X][X][Y]} {H : F[X][Y]}
variable [hHirr : Fact (Irreducible H)] [hHpos : Fact (0 < H.natDegree)]

/-- A finite set of rational places at which a bounded regular element vanishes cannot exceed its
resultant degree unless the element itself is zero in the function field. -/
theorem card_le_weight_mul_degree_of_embedding_ne_zero
    (hH : 0 < H.natDegree) {D B : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (β : 𝒪 H) (hembed : embeddingOf𝒪Into𝑃 H β ≠ 0)
    (hweight : regularWeight hH β D ≤ (WithBot.some B : WithBot ℕ))
    (S : Finset F) (root : ∀ z : F, z ∈ S → rationalRoot (monicize H) z)
    (hvanish : ∀ z (hz : z ∈ S), piZ z (root z hz) β = 0) :
    S.card ≤ B * H.natDegree := by
  classical
  by_contra hcard
  have hsub : (S : Set F) ⊆ rationalVanishingSet β := by
    intro z hz
    exact ⟨root z hz, hvanish z hz⟩
  have hSncard : S.card ≤ Set.ncard (rationalVanishingSet β) := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub
  have hstrict : B * H.natDegree < Set.ncard (rationalVanishingSet β) := by
    omega
  have hncard : (regularWeight hH β D) * H.natDegree <
      (Set.ncard (rationalVanishingSet β) : WithBot ℕ) := by
    refine lt_of_le_of_lt (mul_le_mul_right' hweight H.natDegree) ?_
    exact_mod_cast hstrict
  exact hembed (embedding_eq_zero_of_many_rational_roots hH β D hD hncard)

/-- Scalars of a cell at which either explicit nonmonic Hensel denominator vanishes. -/
noncomputable def denominatorBadSet (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (E : Finset F)
    (root : ∀ z : F, z ∈ E → rationalRoot (monicize H) z) : Finset F :=
  E.filter fun z ⇒ if hz : z ∈ E then
    piZ z (root z hz) (denominatorBase x₀ R H hHyp) = 0 else False

/-- The complement of all denominator-bad places in a cell. -/
noncomputable def denominatorGoodSet (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (E : Finset F)
    (root : ∀ z : F, z ∈ E → rationalRoot (monicize H) z) : Finset F :=
  E.filter fun z ⇒ if hz : z ∈ E then
    piZ z (root z hz) (denominatorBase x₀ R H hHyp) ≠ 0 else False

theorem denominatorBadSet_union_denominatorGoodSet
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (E : Finset F)
    (root : ∀ z : F, z ∈ E → rationalRoot (monicize H) z) :
    denominatorBadSet x₀ R H hHyp E root ∪
        denominatorGoodSet x₀ R H hHyp E root = E := by
  classical
  ext z
  by_cases hz : z ∈ E <;> simp [denominatorBadSet, denominatorGoodSet, hz]
  tauto

/-- Fibres of the support-incidence relation. -/
def supportFiber {I : Type} [DecidableEq I]
    (E : Finset F) (support : F → Finset I) (i : I) : Finset F :=
  E.filter fun z ⇒ i ∈ support z

/-- Coordinates incident to more than `B` members of a scalar family. -/
def richCoordinates {I : Type} [Fintype I] [DecidableEq I]
    (E : Finset F) (support : F → Finset I) (B : ℕ) : Finset I :=
  Finset.univ.filter fun i ⇒ B < (supportFiber E support i).card

lemma sum_supportFiber_card {I : Type} [Fintype I] [DecidableEq I]
    (E : Finset F) (support : F → Finset I) :
    ∑ i : I, (supportFiber E support i).card = ∑ z ∈ E, (support z).card := by
  classical
  simp only [supportFiber, Finset.card_filter, Finset.card_eq_sum_ones]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz ⇒ ?_
  simp [Finset.card_eq_sum_ones]

/-- The exact incidence inequality used at the prize parameters.  A family larger than the
heavy-cell threshold has at least `k+1` coordinates each used by more than the cleared-value
root threshold. -/
theorem targetK_lt_richCoordinates_card
    (E : Finset IRSProfile.Field)
    (support : IRSProfile.Field → Finset IRSProfile.Index)
    (A : ℕ)
    (hsupport : ∀ z ∈ E, (support z).card = 186199)
    (hlarge : (2 * targetDX - 1) * A < E.card) :
    targetK < (richCoordinates E support ((2 * targetK + 1) * A)).card := by
  classical
  let B := (2 * targetK + 1) * A
  let rich := richCoordinates E support B
  by_contra hnot
  have hrich : rich.card ≤ targetK := Nat.le_of_not_gt hnot
  have hfiber_le (i : IRSProfile.Index) :
      (supportFiber E support i).card ≤
        (if i ∈ rich then E.card else 0) + B := by
    by_cases hi : i ∈ rich
    · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [hi])
    · have hi' : (supportFiber E support i).card ≤ B := by
        simpa [rich, richCoordinates, Finset.mem_filter, hi] using
          Nat.le_of_not_gt (show ¬ B < (supportFiber E support i).card by
            simpa [rich, richCoordinates] using hi)
      simpa [hi] using hi'
  have hsum : ∑ i : IRSProfile.Index, (supportFiber E support i).card ≤
      rich.card * E.card + Fintype.card IRSProfile.Index * B := by
    calc
      ∑ i : IRSProfile.Index, (supportFiber E support i).card ≤
          ∑ i : IRSProfile.Index, ((if i ∈ rich then E.card else 0) + B) :=
        Finset.sum_le_sum fun i _ ⇒ hfiber_le i
      _ = rich.card * E.card + Fintype.card IRSProfile.Index * B := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_irrel, Nat.mul_comm]
  have hincidence : 186199 * E.card ≤
      targetK * E.card + targetN * B := by
    have hleft : ∑ z ∈ E, (support z).card = 186199 * E.card := by
      simp_rw [hsupport]
      simp [Nat.mul_comm]
    have hright := hsum
    rw [sum_supportFiber_card, hleft] at hright
    have hcardIndex : Fintype.card IRSProfile.Index = targetN := by
      norm_num [IRSProfile.Index, targetN]
    rw [hcardIndex] at hright
    exact hright.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hrich) _)
  dsimp [B] at hincidence
  norm_num [targetK, targetN, targetDX] at hincidence hlarge
  omega

/-- A convenient fixed-size set of rich coordinates. -/
theorem exists_rich_coordinate_set
    (E : Finset IRSProfile.Field)
    (support : IRSProfile.Field → Finset IRSProfile.Index)
    (A : ℕ)
    (hsupport : ∀ z ∈ E, (support z).card = 186199)
    (hlarge : (2 * targetDX - 1) * A < E.card) :
    ∃ K : Finset IRSProfile.Index,
      K ⊆ richCoordinates E support ((2 * targetK + 1) * A) ∧ K.card = targetK := by
  have hcard : targetK ≤ (richCoordinates E support ((2 * targetK + 1) * A)).card :=
    (targetK_lt_richCoordinates_card E support A hsupport hlarge).le
  obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨K, hK, hKcard⟩

/-! ## A repaired heavy-cell package -/

/-- All per-scalar data attached to one `(R,H)` cell.  No regularity at a scalar is assumed:
zeros of either the leading coefficient or the cleared derivative are charged to the cell core. -/
structure Data
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) where
  scalars : Finset IRSProfile.Field
  decode : ∀ z : {z // z ∈ scalars}, TargetDecode U z.1
  root : ∀ z : IRSProfile.Field, z ∈ scalars → rationalRoot (monicize H) z
  base : ∀ z : {z // z ∈ scalars},
    (root z.1).1 = H.leadingCoeff.eval z.1 * (decode z).polynomial.eval x₀
  factor : ∀ z : {z // z ∈ scalars},
    Polynomial.X - Polynomial.C (decode z).polynomial ∣ specializeR R z.1

/-- The support function associated to cell data. -/
noncomputable def Data.support
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {x₀ : IRSProfile.Field} {R : IRSProfile.Field[X][X][Y]}
    {H : IRSProfile.Field[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : Hypotheses x₀ R H} (C : Data U x₀ R H hHyp)
    (z : IRSProfile.Field) : Finset IRSProfile.Index :=
  if hz : z ∈ C.scalars then (C.decode ⟨z, hz⟩).support else ∅

theorem Data.support_card
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {x₀ : IRSProfile.Field} {R : IRSProfile.Field[X][X][Y]}
    {H : IRSProfile.Field[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : Hypotheses x₀ R H} (C : Data U x₀ R H hHyp)
    {z : IRSProfile.Field} (hz : z ∈ C.scalars) :
    (C.support z).card = 186199 := by
  simp [Data.support, hz, (C.decode ⟨z, hz⟩).support_card]

/-- The degree-`<k` coefficient polynomial of the generic Hensel branch, in the local variable
`S = X-x₀`. -/
noncomputable def henselCoefficientPolynomial (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k : ℕ) : Polynomial (𝑃 H) :=
  ∑ t ∈ Finset.range k, Polynomial.monomial t (alpha x₀ R H hHyp t)

theorem henselCoefficientPolynomial_eval (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k : ℕ) (e : F) :
    (henselCoefficientPolynomial x₀ R H hHyp k).eval (fieldTo𝑃 (H := H) e) =
      ∑ t ∈ Finset.range k,
        alpha x₀ R H hHyp t * fieldTo𝑃 (H := H) (e ^ t) := by
  classical
  simp [henselCoefficientPolynomial, Polynomial.eval_monomial, map_pow]

theorem henselCoefficientPolynomial_coeff (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (k t : ℕ) (ht : t < k) :
    (henselCoefficientPolynomial x₀ R H hHyp k).coeff t = alpha x₀ R H hHyp t := by
  classical
  simp [henselCoefficientPolynomial, Polynomial.coeff_monomial, ht]

theorem henselCoefficientPolynomial_degree_lt (x₀ : F) (R : F[X][X][Y])
    (H : F[X][Y]) (hHyp : Hypotheses x₀ R H) {k : ℕ} (hk : 0 < k) :
    (henselCoefficientPolynomial x₀ R H hHyp k).degree < k := by
  rw [henselCoefficientPolynomial]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by simp [hk])]
  intro t ht
  exact (Polynomial.degree_monomial_le _ _).trans_lt (by
    rw [WithBot.coe_lt_coe, Finset.mem_range] at ⊢ ht
    exact ht)

/-- Undo Taylor recentering. -/
noncomputable def uncenter (x₀ : F) (p : F[X]) : F[X] :=
  (Polynomial.taylorEquiv x₀).symm p

@[simp] theorem taylor_uncenter (x₀ : F) (p : F[X]) :
    Polynomial.taylor x₀ (uncenter x₀ p) = p := by
  exact (Polynomial.taylorEquiv x₀).apply_symm_apply p

@[simp] theorem degree_uncenter (x₀ : F) (p : F[X]) :
    (uncenter x₀ p).degree = p.degree := by
  simp [uncenter]

/-- Crossing the corrected algebraic threshold forces every denominator-good member of a cell
onto one affine polynomial branch.  The removed leading-coefficient and derivative poles
together cost at most one unit `A = (dR+1)dH D` of the cell budget. -/
theorem exists_affine_branch_on_denominatorGood_of_heavy
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (C : Data U x₀ R H hHyp)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.degreeX (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (hheavy : 2 * targetDX * (Bivariate.natDegreeY R + 1) * H.natDegree * D <
      C.scalars.card) :
    ∃ v₀ v₁ : Polynomial IRSProfile.Field,
      v₀.degree < IRSProfile.baseDimension ∧
      v₁.degree < IRSProfile.baseDimension ∧
      ∀ z : {z // z ∈ denominatorGoodSet x₀ R H hHyp C.scalars C.root},
        (C.decode ⟨z.1, (Finset.mem_filter.mp z.2).1⟩).polynomial =
          affinePolynomial v₀ v₁ z.1 := by
  classical
  let dR := Bivariate.natDegreeY R
  let dH := H.natDegree
  let A := (dR + 1) * dH * D
  let good := denominatorGoodSet x₀ R H hHyp C.scalars C.root
  let bad := denominatorBadSet x₀ R H hHyp C.scalars C.root
  have hH : 0 < H.natDegree := Fact.out
  have hdHle : dH ≤ dR := natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hD_Rx0 := evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
  have hWgeneric : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hxigeneric : embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ≠ 0 := by
    rw [embeddingOf𝒪Into𝑃_xi]
    exact mul_ne_zero (pow_ne_zero _ hWgeneric)
      (zeta_ne_zero_of_hypotheses x₀ R H hHyp)
  have hdengeneric : embeddingOf𝒪Into𝑃 H
      (denominatorBase x₀ R H hHyp) ≠ 0 := by
    simp only [denominatorBase, map_mul, embed_regularLeadingCoeff]
    exact mul_ne_zero hWgeneric hxigeneric
  have hxiweight : regularWeight hH (xi x₀ R H hHyp) D ≤
      (WithBot.some (xiBudget x₀ R H D) : WithBot ℕ) :=
    xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hcontent : contentWeight x₀ R H ≤ D - dR := by
    exact contentWeight_le x₀ hH hHyp
      (by simpa [dR, Bivariate.natDegreeY] using hRdeg) hD_Rx0
  have hdHpos : 1 ≤ dH := hH
  have hdenBudget : (D - dH) + xiBudget x₀ R H D ≤ (dR + 1) * D := by
    have hdRpos : 1 ≤ dR := hdHpos.trans hdHle
    have hfactor : D - dH + 1 ≤ D := by omega
    have hxi : xiBudget x₀ R H D ≤ dR * D := by
      unfold xiBudget
      calc
        (R.natDegree - 1) * (D - H.natDegree + 1) + contentWeight x₀ R H
            ≤ (dR - 1) * D + D :=
          Nat.add_le_add
            (by simpa [dR, dH] using Nat.mul_le_mul_left (dR - 1) hfactor)
            (hcontent.trans (Nat.sub_le _ _))
        _ = dR * D := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hdRpos]
    calc
      (D - dH) + xiBudget x₀ R H D ≤ D + dR * D :=
        Nat.add_le_add (Nat.sub_le _ _) hxi
      _ = (dR + 1) * D := by ring
  have hWweight : regularWeight hH (regularLeadingCoeff H) D ≤
      (WithBot.some (D - dH) : WithBot ℕ) := by
    apply regularWeight_le_of_regularWeightLe
    simpa [dH, Bivariate.natDegreeY] using
      regularWeightLe_leadingCoeff_sharp hD_H hH
  have hdenweight : regularWeight hH (denominatorBase x₀ R H hHyp) D ≤
      (WithBot.some ((dR + 1) * D) : WithBot ℕ) := by
    refine (regularWeight_mul_le' hD_H hH hWweight hxiweight).trans ?_
    simpa using hdenBudget
  have hbad : bad.card ≤ A := by
    have hroot := card_le_weight_mul_degree_of_embedding_ne_zero hH hD_H
      (denominatorBase x₀ R H hHyp) hdengeneric hdenweight bad
      (fun z hz ⇒ C.root z (Finset.mem_filter.mp hz).1) (by
        intro z hz
        have hzcell : z ∈ C.scalars := (Finset.mem_filter.mp hz).1
        simpa [denominatorBadSet, hzcell] using (Finset.mem_filter.mp hz).2)
    calc
      bad.card ≤ ((dR + 1) * D) * H.natDegree := hroot
      _ = A := by simp [A]; ring
  have hpartition : bad.card + good.card = C.scalars.card := by
    have hdis : Disjoint bad good := by
      refine Finset.disjoint_left.mpr ?_
      intro z hzb hzg
      exact (Finset.mem_filter.mp hzg).2 (Finset.mem_filter.mp hzb).2
    rw [← Finset.card_union_of_disjoint hdis,
      denominatorBadSet_union_denominatorGoodSet]
  have hgoodLarge : (2 * targetDX - 1) * A < good.card := by
    dsimp [dR, dH, A] at hheavy ⊢
    dsimp [bad, good] at hbad hpartition
    omega
  let support : IRSProfile.Field → Finset IRSProfile.Index := C.support
  have hsupport : ∀ z ∈ good, (support z).card = 186199 := by
    intro z hz
    exact C.support_card (Finset.mem_filter.mp hz).1
  obtain ⟨K, hKrich, hKcard⟩ := exists_rich_coordinate_set good support A hsupport hgoodLarge
  let shifted : IRSProfile.Index → IRSProfile.Field := fun i ⇒ IRSProfile.domain i - x₀
  have hshifted : Set.InjOn shifted K := by
    intro i hi j hj hij
    apply IRSProfile.domain.injective
    dsimp [shifted] at hij
    exact sub_right_injective hij
  let a₀ : Polynomial IRSProfile.Field := Lagrange.interpolate K shifted (U 0)
  let a₁ : Polynomial IRSProfile.Field := Lagrange.interpolate K shifted (U 1)
  have ha₀deg : a₀.degree < targetK := by
    simpa [a₀, hKcard] using Lagrange.degree_interpolate_lt (U 0) hshifted
  have ha₁deg : a₁.degree < targetK := by
    simpa [a₁, hKcard] using Lagrange.degree_interpolate_lt (U 1) hshifted
  have hvalue (i : IRSProfile.Index) (hi : i ∈ K) :
      (henselCoefficientPolynomial x₀ R H hHyp targetK).eval
          (fieldTo𝑃 (H := H) (shifted i)) =
        liftToFunctionField (H := H)
          (Polynomial.C (U 0 i) + Polynomial.X * Polynomial.C (U 1 i)) := by
    have hirich := hKrich hi
    have hrich : (2 * targetK + 1) * A <
        (supportFiber good support i).card :=
      (Finset.mem_filter.mp hirich).2
    let β := clearedValue x₀ R H hHyp targetK (shifted i) (U 0 i) (U 1 i)
    have hβweight : regularWeight hH β D ≤
        (WithBot.some ((2 * targetK + 1) * (dR + 1) * D) : WithBot ℕ) := by
      simpa [β, dR] using clearedValue_weight_le x₀ R H hHyp hH hD_H hD_R hRdeg
        targetK (shifted i) (U 0 i) (U 1 i)
    have hvanish : ∀ z (hz : z ∈ supportFiber good support i),
        piZ z (C.root z ((Finset.mem_filter.mp
          (Finset.mem_filter.mp hz).1).1)) β = 0 := by
      intro z hz
      have hzgood : z ∈ good := (Finset.mem_filter.mp hz).1
      have hzcell : z ∈ C.scalars := (Finset.mem_filter.mp hzgood).1
      let rz := C.root z hzcell
      have hzden : piZ z rz (denominatorBase x₀ R H hHyp) ≠ 0 := by
        simpa [good, denominatorGoodSet, hzcell, rz] using
          (Finset.mem_filter.mp hzgood).2
      have hWz : H.leadingCoeff.eval z ≠ 0 := by
        intro hzero
        apply hzden
        simp [denominatorBase, hzero]
      have hzxi : piZ z rz (xi x₀ R H hHyp) ≠ 0 := by
        intro hzero
        apply hzden
        simp [denominatorBase, hzero]
      have hzi : i ∈ (C.decode ⟨z, hzcell⟩).support := by
        simpa [support, Data.support, hzcell] using (Finset.mem_filter.mp hz).2
      have hread (t : ℕ) :
          alphaAt x₀ R H hHyp z rz hWz hzxi t =
            (Polynomial.taylor x₀ (C.decode ⟨z, hzcell⟩).polynomial).coeff t :=
        alphaAt_eq_taylorCoeff x₀ R H hHyp z rz hWz hzxi
          (C.decode ⟨z, hzcell⟩).polynomial (C.base ⟨z, hzcell⟩)
          (C.factor ⟨z, hzcell⟩) t
      have hPnat : (C.decode ⟨z, hzcell⟩).polynomial.natDegree < targetK := by
        by_cases hp : (C.decode ⟨z, hzcell⟩).polynomial = 0
        · simp [hp, targetK]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (by
            simpa [targetK, IRSProfile.baseDimension] using
              (C.decode ⟨z, hzcell⟩).degree_lt)
      have htaylor :
          ∑ t ∈ Finset.range targetK,
              (Polynomial.taylor x₀ (C.decode ⟨z, hzcell⟩).polynomial).coeff t *
                (shifted i) ^ t =
            (C.decode ⟨z, hzcell⟩).polynomial.eval (IRSProfile.domain i) := by
        have he := (Polynomial.taylor x₀
          (C.decode ⟨z, hzcell⟩).polynomial).eval_eq_sum_range' (by
            simpa using hPnat) (shifted i)
        rw [Polynomial.taylor_eval_sub] at he
        simpa [shifted] using he.symm
      have hfold : ∑ t ∈ Finset.range targetK,
          alphaAt x₀ R H hHyp z rz hWz hzxi t * (shifted i) ^ t =
            U 0 i + z * U 1 i := by
        simp_rw [hread]
        rw [htaylor, (C.decode ⟨z, hzcell⟩).agreement i hzi]
      exact piZ_clearedValue_eq_zero x₀ R H hHyp targetK (shifted i)
        (U 0 i) (U 1 i) z rz hWz hzxi hfold
    have hβzero : embeddingOf𝒪Into𝑃 H β = 0 := by
      by_contra hne
      have hle := card_le_weight_mul_degree_of_embedding_ne_zero hH hD_H β hne hβweight
        (supportFiber good support i)
        (fun z hz ⇒ C.root z ((Finset.mem_filter.mp
          (Finset.mem_filter.mp hz).1).1)) hvanish
      have hthreshold :
          ((2 * targetK + 1) * (dR + 1) * D) * H.natDegree =
            (2 * targetK + 1) * A := by simp [A, dH]; ring
      rw [hthreshold] at hle
      omega
    rw [β, embed_clearedValue x₀ R H hHyp targetK (shifted i) (U 0 i) (U 1 i)
      hWgeneric hxigeneric] at hβzero
    have hden : liftToFunctionField (H := H) H.leadingCoeff ^ (targetK + 1) *
        embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ^
          henselDenominatorExponent targetK ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hWgeneric) (pow_ne_zero _ hxigeneric)
    have hdiff := (mul_eq_zero.mp hβzero).resolve_left hden
    rw [sub_eq_zero] at hdiff
    simpa [henselCoefficientPolynomial_eval] using hdiff
  have hpoly : henselCoefficientPolynomial x₀ R H hHyp targetK =
      a₀.map (fieldTo𝑃 (H := H)) +
        Polynomial.C (liftToFunctionField (H := H) Polynomial.X) *
          a₁.map (fieldTo𝑃 (H := H)) := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq K
      (fun i hi j hj hij ⇒ Subtype.ext <| (fieldTo𝑃 (H := H)).injective <|
        hshifted hi hj hij)
    · simpa [hKcard] using
        henselCoefficientPolynomial_degree_lt x₀ R H hHyp
          (by norm_num [targetK])
    · refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · simpa [hKcard] using
          (Polynomial.degree_map_le (p := a₀) (f := fieldTo𝑃 (H := H))).trans_lt ha₀deg
      · refine (Polynomial.degree_mul_le _ _).trans_lt ?_
        simpa [hKcard] using ha₁deg
    · intro i hi
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval_map,
        Lagrange.eval_interpolate_at_node (U 0) hshifted hi,
        Lagrange.eval_interpolate_at_node (U 1) hshifted hi,
        hvalue i hi]
      simp [fieldTo𝑃, map_sub]
  let v₀ := uncenter x₀ a₀
  let v₁ := uncenter x₀ a₁
  have hv₀ : v₀.degree < IRSProfile.baseDimension := by
    simpa [v₀, degree_uncenter, targetK, IRSProfile.baseDimension] using ha₀deg
  have hv₁ : v₁.degree < IRSProfile.baseDimension := by
    simpa [v₁, degree_uncenter, targetK, IRSProfile.baseDimension] using ha₁deg
  refine ⟨v₀, v₁, hv₀, hv₁, ?_⟩
  intro z
  have hzgood : z.1 ∈ good := z.2
  have hzcell : z.1 ∈ C.scalars := (Finset.mem_filter.mp hzgood).1
  let rz := C.root z.1 hzcell
  have hzden : piZ z.1 rz (denominatorBase x₀ R H hHyp) ≠ 0 := by
    simpa [good, denominatorGoodSet, hzcell, rz] using
      (Finset.mem_filter.mp hzgood).2
  have hWz : H.leadingCoeff.eval z.1 ≠ 0 := by
    intro hzero
    apply hzden
    simp [denominatorBase, hzero]
  have hzxi : piZ z.1 rz (xi x₀ R H hHyp) ≠ 0 := by
    intro hzero
    apply hzden
    simp [denominatorBase, hzero]
  have hcoeff (t : ℕ) (ht : t < targetK) :
      (Polynomial.taylor x₀ (C.decode ⟨z.1, hzcell⟩).polynomial).coeff t =
        (a₀ + Polynomial.C z.1 * a₁).coeff t := by
    have hread := alphaAt_eq_taylorCoeff x₀ R H hHyp z.1 rz hWz hzxi
      (C.decode ⟨z.1, hzcell⟩).polynomial (C.base ⟨z.1, hzcell⟩)
      (C.factor ⟨z.1, hzcell⟩) t
    have halpha := congrArg (fun p : Polynomial (𝑃 H) ⇒ p.coeff t) hpoly
    rw [henselCoefficientPolynomial_coeff x₀ R H hHyp targetK t ht,
      Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      Polynomial.coeff_map] at halpha
    have hlocal : localAlpha x₀ R H hHyp t =
        algebraMap (𝒪 H) (LocalRing x₀ R H hHyp)
          (regularAffine H (a₀.coeff t) (a₁.coeff t)) := by
      apply toFunctionField_injective x₀ R H hHyp
      rw [toFunctionField_localAlpha, toFunctionField_algebraMap, embed_regularAffine]
      simpa [fieldTo𝑃] using halpha
    have hplace := congrArg
      (toPlace x₀ R H hHyp z.1 rz
        (denominatorBase_good x₀ R H hHyp z.1 rz hWz hzxi)) hlocal
    rw [toPlace_localAlpha, toPlace_algebraMap, piZ_regularAffine] at hplace
    rw [← hread, hplace]
    simp
  have hTaylor : Polynomial.taylor x₀ (C.decode ⟨z.1, hzcell⟩).polynomial =
      a₀ + Polynomial.C z.1 * a₁ := by
    apply Polynomial.ext
    intro t
    by_cases ht : t < targetK
    · exact hcoeff t ht
    · have hPnat : (C.decode ⟨z.1, hzcell⟩).polynomial.natDegree < targetK := by
        by_cases hp : (C.decode ⟨z.1, hzcell⟩).polynomial = 0
        · simp [hp, targetK]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (by
            simpa [targetK, IRSProfile.baseDimension] using
              (C.decode ⟨z.1, hzcell⟩).degree_lt)
      have ha₀nat : a₀.natDegree < targetK := by
        by_cases hp : a₀ = 0
        · simp [hp, targetK]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr ha₀deg
      have ha₁nat : a₁.natDegree < targetK := by
        by_cases hp : a₁ = 0
        · simp [hp, targetK]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr ha₁deg
      rw [Polynomial.coeff_add, Polynomial.coeff_mul_C,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hPnat.trans_le (Nat.le_of_not_gt ht)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (ha₀nat.trans_le (Nat.le_of_not_gt ht)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (ha₁nat.trans_le (Nat.le_of_not_gt ht))]
      simp
  apply Polynomial.taylor_injective x₀
  rw [hTaylor]
  simp [affinePolynomial, v₀, v₁, map_add, map_mul]

/-- The complete per-cell bound: all denominator-bad places cost one unit `A`, and the good part
costs at most one scalar per coordinate.  Since `A ≤ 2*DX*A`, this is absorbed by the advertised
`2*DX*A + n` budget. -/
theorem card_cell_le_corrected_core_add_targetN
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (C : Data U x₀ R H hHyp)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.degreeX (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    C.scalars.card ≤
      2 * targetDX * (Bivariate.natDegreeY R + 1) * H.natDegree * D + targetN := by
  classical
  let core := 2 * targetDX * (Bivariate.natDegreeY R + 1) * H.natDegree * D
  by_cases hsmall : C.scalars.card ≤ core
  · omega
  · have hheavy : core < C.scalars.card := Nat.lt_of_not_ge hsmall
    obtain ⟨v₀, v₁, hv₀, hv₁, hbranch⟩ :=
      exists_affine_branch_on_denominatorGood_of_heavy U x₀ R H hHyp C
        hD_H hD_R hRdeg hheavy
    let good := denominatorGoodSet x₀ R H hHyp C.scalars C.root
    let bad := denominatorBadSet x₀ R H hHyp C.scalars C.root
    have hgood : good.card ≤ targetN := by
      apply card_cell_le_targetN_of_affine_branch U good
        (fun z ⇒ C.decode ⟨z.1, (Finset.mem_filter.mp z.2).1⟩) v₀ v₁ hv₀ hv₁
      exact hbranch
    have hpartition : bad.card + good.card = C.scalars.card := by
      have hdis : Disjoint bad good := by
        refine Finset.disjoint_left.mpr ?_
        intro z hzb hzg
        exact (Finset.mem_filter.mp hzg).2 (Finset.mem_filter.mp hzb).2
      rw [← Finset.card_union_of_disjoint hdis,
        denominatorBadSet_union_denominatorGoodSet]
    have hbadcore : bad.card ≤ core := by
      have hH : 0 < H.natDegree := Fact.out
      have hWgeneric : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
        liftToFunctionField_leadingCoeff_ne_zero (H := H)
      have hxigeneric : embeddingOf𝒪Into𝑃 H (xi x₀ R H hHyp) ≠ 0 := by
        rw [embeddingOf𝒪Into𝑃_xi]
        exact mul_ne_zero (pow_ne_zero _ hWgeneric)
          (zeta_ne_zero_of_hypotheses x₀ R H hHyp)
      have hD_Rx0 := evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
      have hxiweight := xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
      have hdengeneric : embeddingOf𝒪Into𝑃 H
          (denominatorBase x₀ R H hHyp) ≠ 0 := by
        simp only [denominatorBase, map_mul, embed_regularLeadingCoeff]
        exact mul_ne_zero hWgeneric hxigeneric
      have hWweight : regularWeight hH (regularLeadingCoeff H) D ≤
          (WithBot.some (D - H.natDegree) : WithBot ℕ) := by
        apply regularWeight_le_of_regularWeightLe
        simpa [Bivariate.natDegreeY] using
          regularWeightLe_leadingCoeff_sharp hD_H hH
      have hdenweight : regularWeight hH (denominatorBase x₀ R H hHyp) D ≤
          (WithBot.some ((Bivariate.natDegreeY R + 1) * D) : WithBot ℕ) := by
        refine (regularWeight_mul_le' hD_H hH hWweight hxiweight).trans ?_
        rw [WithBot.coe_le_coe]
        have hc := contentWeight_le x₀ hH hHyp
          (by simpa [Bivariate.natDegreeY] using hRdeg) hD_Rx0
        unfold xiBudget
        have hfactor : D - H.natDegree + 1 ≤ D := by omega
        have hfirst :
            (R.natDegree - 1) * (D - H.natDegree + 1) ≤
              (R.natDegree - 1) * D :=
          Nat.mul_le_mul_left _ hfactor
        have hRpos : 1 ≤ R.natDegree := by
          simpa [Bivariate.natDegreeY] using hRdeg.trans' (by omega)
        calc
          (D - H.natDegree) +
                ((R.natDegree - 1) * (D - H.natDegree + 1) +
                  contentWeight x₀ R H)
              ≤ D + ((R.natDegree - 1) * D + D) :=
            Nat.add_le_add (Nat.sub_le _ _)
              (Nat.add_le_add hfirst (hc.trans (Nat.sub_le _ _)))
          _ = (R.natDegree + 1) * D := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hRpos]
            ring
      have hb := card_le_weight_mul_degree_of_embedding_ne_zero hH hD_H
        (denominatorBase x₀ R H hHyp) hdengeneric hdenweight bad
        (fun z hz ⇒ C.root z (Finset.mem_filter.mp hz).1)
        (fun z hz ⇒ by
          have hzcell : z ∈ C.scalars := (Finset.mem_filter.mp hz).1
          simpa [denominatorBadSet, hzcell] using (Finset.mem_filter.mp hz).2)
      have hunit : bad.card ≤ (Bivariate.natDegreeY R + 1) * D * H.natDegree :=
        hb
      dsimp [core]
      have hDX : 1 ≤ 2 * targetDX := by norm_num [targetDX]
      nlinarith
    dsimp [good, bad] at hgood hpartition hbadcore
    dsimp [core]
    omega

end HeavyCell
end HeavyCell
end ProximityPrize.SubmissionLower.RF6317
