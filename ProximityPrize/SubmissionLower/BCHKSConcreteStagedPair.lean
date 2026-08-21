import ProximityPrize.SubmissionLower.BCHKSStagedPairAssembly
import ProximityPrize.SubmissionLower.BCHKSSingleFactorGood

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The outer integration theorem: the only missing input is a quantitative
primitive-specialization certificate for each possible first-stage factor. -/
theorem exists_concrete_staged_pair_of_certificates
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (cert : ∀ R : Polynomial (Polynomial (Polynomial F)),
      ClearedPrimitiveCertificate F R)
    (hcertDegree : ∀ R : Polynomial (Polynomial (Polynomial F)),
      (cert R).obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hfactorXDegree : ∀ (R : Polynomial (Polynomial (Polynomial F))) (x : F),
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 453561)
    (hchar : 801 < ringChar F)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 801)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 453561)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 104951682)
    (hcard : 2 * 104951682 * 453561 * 801 ^ 2 +
      (bchksErrors + 1) * 801 + 2 * 453561 * 801 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset F,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval x₀ (P z)) z = 0) ∧
      2 * 104951682 * 453561 * R.natDegree * H.natDegree +
        (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R x₀ ∧
      R.natDegree ≤ 801 ∧ H.natDegree ≤ 801 ∧
      Polynomial.Bivariate.totalDegree H ≤ 453561 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 453561 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 104951682) ∧
      RationalFunctions.HenselNumerators.Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 453561 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let good : ∀ R : Polynomial (Polynomial (Polynomial F)),
      Irreducible R → 0 < R.natDegree → R.natDegree ≤ 801 →
      ∃ x₀ : F, ∃ Bad : Finset F,
        Bad.card ≤ 2 * R.natDegree * 453561 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).IsPrimitive ∧
        (∀ z ∉ Bad, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
          Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
    intro R hR hp hd
    apply exists_single_factor_good R hR hp
      (lt_of_le_of_lt hd hchar) (cert R)
      R.natDegree 453561 (hcertDegree R) (hfactorXDegree R)
  let pick : Polynomial (Polynomial (Polynomial F)) → F × Finset F := fun R =>
    if h : Irreducible R ∧ 0 < R.natDegree ∧ R.natDegree ≤ 801 then
      (Classical.choose (good R h.1 h.2.1 h.2.2),
        Classical.choose (Classical.choose_spec (good R h.1 h.2.1 h.2.2)))
    else (0, ∅)
  let x₀ := fun R => (pick R).1
  let Bad := fun R => (pick R).2
  have hpick : ∀ R (hi : Irreducible R) (hp : 0 < R.natDegree) (hd : R.natDegree ≤ 801),
      (Bad R).card ≤ 2 * R.natDegree * 453561 ∧
      (triSpecializeX R (x₀ R)).natDegree = R.natDegree ∧
      triSpecializeX R (x₀ R) ≠ 0 ∧
      (triSpecializeX R (x₀ R)).IsPrimitive ∧
      (∀ z ∉ Bad R, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R (x₀ R)) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z) ≠ 0) := by
    intro R hi hp hd
    simpa [x₀, Bad, pick, hi, hp, hd] using
      Classical.choose_spec (Classical.choose_spec (good R hi hp hd))
  have hRdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.natDegree ≤ 801 := by
    intro R hRQ
    calc
      R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 801 := hQY
  let G : StagedGoodFamily Q S := {
    x₀ := x₀
    Bad := Bad
    badCap := fun R => 2 * R.natDegree * 453561
    specialize_ne_zero := by
      intro R hRQ hp
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.1
    primitive := by
      intro R hRQ hp
      rw [Polynomial.Bivariate.evalX_eq_map]
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.1
    bad_card := by
      intro R hRQ hp
      exact (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).1
    bad_cap := by simp
    second_ne_zero := by
      intro R hRQ hp z hz
      intro heq
      have hs := (hpick R (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.2
        z (Finset.mem_sdiff.mp hz).2 0
      have hder : triSpecializeX R.derivative (x₀ R) =
          (triSpecializeX R (x₀ R)).derivative := by
        simp [triSpecializeX, Polynomial.derivative_map]
      have hd : biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z = 0 := by
        rw [hder]
        simpa [biSpecializeZ, Polynomial.derivative_map] using
          congrArg Polynomial.derivative heq
      exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
  }
  obtain ⟨R, H, T, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
      hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp⟩ :=
    exists_staged_pair_with_setup S P Q G hQ hQeval hQz hQY hQYZ
      hQweightedX hcard
  have hg := hpick R hRi hp hRd
  exact ⟨R, H, T, x₀ R, Bad R, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
    hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp, hg.1, hg.2.2.2.2⟩


/-- Effective-obstruction overload of the concrete staged-pair theorem. -/
theorem exists_concrete_staged_pair_of_effective_obstructions
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (cert : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q → 0 < R.natDegree →
      EffectivePrimitiveObstruction F R)
    (hcertDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (hp : 0 < R.natDegree),
      (cert R hRQ hp).obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hfactorXDegree : ∀ (R : Polynomial (Polynomial (Polynomial F)))
      (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (hp : 0 < R.natDegree)
      (x : F),
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 453561)
    (hchar : 801 < ringChar F)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 801)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 453561)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 104951682)
    (hcard : (2 * 104951682 * 453561) * 801 +
      (634000 * 453561) * 801 ^ 2 +
      (bchksErrors + 1) * 801 + 2 * 453561 * 801 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset F,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval x₀ (P z)) z = 0) ∧
      (if R.natDegree = 1 then 2 * 104951682 * 453561 else 634000 * 453561) *
        R.natDegree * H.natDegree + (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R x₀ ∧
      R.natDegree ≤ 801 ∧ H.natDegree ≤ 801 ∧
      Polynomial.Bivariate.totalDegree H ≤ 453561 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 453561 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 104951682) ∧
      RationalFunctions.HenselNumerators.Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 453561 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let good : ∀ R : Polynomial (Polynomial (Polynomial F)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q →
      Irreducible R → 0 < R.natDegree → R.natDegree ≤ 801 →
      ∃ x₀ : F, ∃ Bad : Finset F,
        Bad.card ≤ 2 * R.natDegree * 453561 ∧
        (triSpecializeX R x₀).natDegree = R.natDegree ∧
        triSpecializeX R x₀ ≠ 0 ∧
        (triSpecializeX R x₀).IsPrimitive ∧
        (∀ z ∉ Bad, ∀ y,
          Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
          Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
    intro R hRQ hR hp hd
    apply exists_single_factor_good_effective R hR hp
      (lt_of_le_of_lt hd hchar) (cert R hRQ hp)
      R.natDegree 453561 (hcertDegree R hRQ hp) (hfactorXDegree R hRQ hp)
  let pick : Polynomial (Polynomial (Polynomial F)) → F × Finset F := fun R =>
    if h : R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        Irreducible R ∧ 0 < R.natDegree ∧ R.natDegree ≤ 801 then
      (Classical.choose (good R h.1 h.2.1 h.2.2.1 h.2.2.2),
        Classical.choose (Classical.choose_spec (good R h.1 h.2.1 h.2.2.1 h.2.2.2)))
    else (0, ∅)
  let x₀ := fun R => (pick R).1
  let Bad := fun R => (pick R).2
  have hpick : ∀ R (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
      (hi : Irreducible R) (hp : 0 < R.natDegree) (hd : R.natDegree ≤ 801),
      (Bad R).card ≤ 2 * R.natDegree * 453561 ∧
      (triSpecializeX R (x₀ R)).natDegree = R.natDegree ∧
      triSpecializeX R (x₀ R) ≠ 0 ∧
      (triSpecializeX R (x₀ R)).IsPrimitive ∧
      (∀ z ∉ Bad R, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R (x₀ R)) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z) ≠ 0) := by
    intro R hRQ hi hp hd
    simpa [x₀, Bad, pick, hRQ, hi, hp, hd] using
      Classical.choose_spec (Classical.choose_spec (good R hRQ hi hp hd))
  have hRdeg : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      R.natDegree ≤ 801 := by
    intro R hRQ
    calc
      R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
          A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simpa using hRQ)
      _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
      _ ≤ 801 := hQY
  let G : StagedGoodFamily Q S := {
    x₀ := x₀
    Bad := Bad
    badCap := fun R => 2 * R.natDegree * 453561
    specialize_ne_zero := by
      intro R hRQ hp
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.1
    primitive := by
      intro R hRQ hp
      rw [Polynomial.Bivariate.evalX_eq_map]
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.1
    bad_card := by
      intro R hRQ hp
      exact (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).1
    bad_cap := by simp
    second_ne_zero := by
      intro R hRQ hp z hz
      intro heq
      have hs := (hpick R hRQ (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp (hRdeg R hRQ)).2.2.2.2
        z (Finset.mem_sdiff.mp hz).2 0
      have hder : triSpecializeX R.derivative (x₀ R) =
          (triSpecializeX R (x₀ R)).derivative := by
        simp [triSpecializeX, Polynomial.derivative_map]
      have hd : biSpecializeZ (triSpecializeX R.derivative (x₀ R)) z = 0 := by
        rw [hder]
        simpa [biSpecializeZ, Polynomial.derivative_map] using
          congrArg Polynomial.derivative heq
      exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
  }
  let A : Polynomial (Polynomial (Polynomial F)) → Nat := fun R =>
    if R.natDegree = 1 then 2 * 104951682 * 453561 else 634000 * 453561
  have hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (A R * R.natDegree ^ 2 + (bchksErrors + 1) * R.natDegree +
          G.badCap R)) < S.card := by
    apply (positive_normalizedFactors_piecewise_cap_le Q hQ G.badCap
      (2 * 104951682 * 453561) (634000 * 453561) (bchksErrors + 1) 453561 801
      hQY ?_).trans_lt hcard
    intro R hR
    have hm := Finset.mem_filter.mp hR
    exact G.bad_cap R (by simpa using hm.1) hm.2
  obtain ⟨R, H, T, hRQ, hp, hHR, hHp, hTS, hTbad, hvan, hmargin,
      hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp⟩ :=
    exists_staged_pair_with_setup_var S P Q G A hQ hQeval hQz hQY hQYZ
      hQweightedX hglobal
  have hg := hpick R hRQ hRi hp hRd
  exact ⟨R, H, T, x₀ R, Bad R, hRQ, hp, hHR, hHp, hTS, hTbad, hvan,
    by simpa [A] using hmargin,
    hRi, hHi, hdiv, hRd, hHd, hHtot, hRXtot, hw, hHyp, hg.1, hg.2.2.2.2⟩

end ProximityPrize.SubmissionLower
