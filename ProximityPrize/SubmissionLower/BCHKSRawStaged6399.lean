import ProximityPrize.SubmissionLower.BCHKSConcreteStagedPair
import ProximityPrize.SubmissionLower.BCHKSRawAlignment6395
import ProximityPrize.SubmissionLower.BCHKSPairSetupRaw

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Concrete good-specialization construction followed by the raw pair-cost
selector for the 63.99 box. -/
theorem exists_concrete_raw_staged_pair_6399
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (cert : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q → 0 < R.natDegree →
      EffectivePrimitiveObstruction F R)
    (hcertDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (hp : 0 < R.natDegree),
      (cert R hRQ hp).obstruction.natDegree + (factorXObstruction R).natDegree <
        Fintype.card F)
    (hfactorXDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (_hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (_hp : 0 < R.natDegree)
      (x : F),
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 13141403)
    (hchar : 5280 < ringChar F)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 5279)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 13141403)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hcard : 632746 * (2 * 5279 * 13141402) +
      (76770 + 1) * 5279 + 2 * 13141403 * 5279 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset F,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval x₀ (P z)) z = 0) ∧
      632746 * SecondStageCapacity.rawPairUnit R.natDegree 13141402 H +
        (76770 + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R x₀ ∧
      R.natDegree ≤ 5279 ∧ H.natDegree ≤ 5279 ∧
      Polynomial.Bivariate.totalDegree H ≤ 13141402 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 13141402 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + 131071 * j < 692001142) ∧
      Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 13141403 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let good : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q →
      Irreducible R → 0 < R.natDegree → R.natDegree ≤ 5279 →
      ∃ x₀ : F, ∃ Bad : Finset F,
        Bad.card ≤ 2 * R.natDegree * 13141403 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).IsPrimitive ∧
        (∀ z ∉ Bad, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
          Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
    intro R hRQ hR hp hd
    apply exists_single_factor_good_effective R hR hp
      (hd.trans_lt (by omega)) (cert R hRQ hp)
      R.natDegree 13141403 (hcertDegree R hRQ hp) (hfactorXDegree R hRQ hp)
  let pick : Polynomial (Polynomial (Polynomial F)) → F × Finset F := fun R =>
    if h : R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        Irreducible R ∧ 0 < R.natDegree ∧ R.natDegree ≤ 5279 then
      (Classical.choose (good R h.1 h.2.1 h.2.2.1 h.2.2.2),
        Classical.choose (Classical.choose_spec (good R h.1 h.2.1 h.2.2.1 h.2.2.2)))
    else (0, ∅)
  let x₀ := fun R => (pick R).1
  let Bad := fun R => (pick R).2
  have hRdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.natDegree ≤ 5279 := by
    intro R hRQ
    calc
      R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 5279 := hQY
  have hpick : ∀ R (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
      (hi : Irreducible R) (hp : 0 < R.natDegree),
      (Bad R).card ≤ 2 * R.natDegree * 13141403 ∧
      (triSpecializeX R (x₀ R)).natDegree = R.natDegree ∧
      triSpecializeX R (x₀ R) ≠ 0 ∧
      (triSpecializeX R (x₀ R)).IsPrimitive ∧
      (∀ z ∉ Bad R, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R (x₀ R)) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z) ≠ 0) := by
    intro R hRQ hi hp
    simpa [x₀, Bad, pick, hRQ, hi, hp, hRdeg R hRQ] using
      Classical.choose_spec (Classical.choose_spec (good R hRQ hi hp (hRdeg R hRQ)))
  let badCap : Polynomial (Polynomial (Polynomial F)) → Nat :=
    fun R => 2 * R.natDegree * 13141403
  let pairCost : Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) → Nat := fun R H =>
    632746 * SecondStageCapacity.rawPairUnit R.natDegree 13141402 H
  have hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → ∀ z ∈ S \ Bad R,
        biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0 := by
    intro R hRQ hp z hz heq
    have hs := (hpick R hRQ
      (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp).2.2.2.2
      z (Finset.mem_sdiff.mp hz).2 0
    have hder : triSpecializeX R.derivative (x₀ R) =
        (triSpecializeX R (x₀ R)).derivative := by
      simp [triSpecializeX, Polynomial.derivative_map]
    have hd : biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z = 0 := by
      rw [hder]
      simpa [biSpecializeZ, Polynomial.derivative_map] using
        congrArg Polynomial.derivative heq
    exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)
  have hsumdeg : (∑ R ∈ Rs, R.natDegree) ≤ 5279 := by
    calc
      _ ≤ ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          R.natDegree := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (by simp)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 5279 := hQY
  have hpoint : ∀ R ∈ Rs,
      ((∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
          (triSpecializeX R (x₀ R))).toFinset.filter (fun H => 0 < H.natDegree),
          (pairCost R H + (76770 + 1))) + badCap R) ≤
        (632746 * (2 * 13141402) + (76770 + 1) + 2 * 13141403) * R.natDegree := by
    intro R hRs
    have hm := Finset.mem_filter.mp hRs
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by simpa [Rs] using hm.1
    have hi := (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
    have hg := hpick R hRQ hi hm.2
    have hinner := SecondStageCapacity.normalized_raw_pair_sum_le
      (triSpecializeX R (x₀ R)) hg.2.2.1 632746 R.natDegree 13141402
      (76770 + 1) (by rw [hg.2.1]) (by
        have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ hQYZ
        have hlt := totalDegree_triSpecializeX_lt R (x₀ R) 13141403 (by norm_num) hRYZ
        omega)
    dsimp [pairCost, badCap]
    calc
      _ ≤ (632746 * (2 * R.natDegree * 13141402) +
          (76770 + 1) * R.natDegree) + 2 * R.natDegree * 13141403 :=
        Nat.add_le_add_right hinner _
      _ = (632746 * (2 * 13141402) + (76770 + 1) + 2 * 13141403) *
          R.natDegree := by ring
  have hglobal :
      (∑ R ∈ Rs,
        ((∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R (x₀ R))).toFinset.filter (fun H => 0 < H.natDegree),
            (pairCost R H + (76770 + 1))) + badCap R)) < S.card := by
    calc
      _ ≤ ∑ R ∈ Rs,
          (632746 * (2 * 13141402) + (76770 + 1) + 2 * 13141403) *
            R.natDegree := Finset.sum_le_sum hpoint
      _ = (632746 * (2 * 13141402) + (76770 + 1) + 2 * 13141403) *
          (∑ R ∈ Rs, R.natDegree) := by rw [Finset.mul_sum]
      _ ≤ (632746 * (2 * 13141402) + (76770 + 1) + 2 * 13141403) * 5279 :=
        Nat.mul_le_mul_left _ hsumdeg
      _ < S.card := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard
  obtain ⟨R, H, T, hRQ, hRp, hHR, hHp, hTS, hTbad, hvan, hmargin⟩ :=
    exists_concrete_staged_factor_selection_by_pair S P Q x₀ Bad badCap pairCost
      (76770 + 1) hQeval hQz
      (fun R hRQ hp => (hpick R hRQ
        (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp).1)
      hsecond (by simpa [Rs] using hglobal)
  have hg := hpick R hRQ
    (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hRp
  have hprim : (Polynomial.Bivariate.evalX (Polynomial.C (x₀ R)) R).IsPrimitive := by
    simpa [triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using hg.2.2.2.1
  have hs := bchks_pair_setup_raw_of_selected_factors Q R H (x₀ R)
    5279 13141403 131071 692001142 (by norm_num) hQ hRQ hHR hHp hQY hQYZ
    hQweightedX hprim
  rcases hs with ⟨hRi, hHi, -, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp⟩
  exact ⟨R, H, T, x₀ R, Bad R, hRQ, hRp, hHR, hHp, hTS, hTbad, hvan,
    by simpa [pairCost] using hmargin, hRi, hHi, hdiv, hRd, hHd, hHtot,
    hRXtot, hw, hHyp, hg.1, hg.2.2.2.2⟩

end ProximityPrize.SubmissionLower
