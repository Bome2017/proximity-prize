import ProximityPrize.SubmissionLower.BCHKSStagedConcrete
import ProximityPrize.SubmissionLower.BCHKSStagedArithmetic
import ProximityPrize.SubmissionLower.BCHKSPairSetupConcrete

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Uniform good-specialization data for the positive normalized factors of
`Q`, relative to the source set on which staged selection is performed. -/
structure StagedGoodFamily
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (S : Finset F) where
  x₀ : Polynomial (Polynomial (Polynomial F)) → F
  Bad : Polynomial (Polynomial (Polynomial F)) → Finset F
  badCap : Polynomial (Polynomial (Polynomial F)) → Nat
  specialize_ne_zero : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → triSpecializeX R (x₀ R) ≠ 0
  primitive : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree →
      (Polynomial.Bivariate.evalX (Polynomial.C (x₀ R)) R).IsPrimitive
  bad_card : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → (Bad R).card ≤ badCap R
  bad_cap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → badCap R ≤ 2 * R.natDegree * 63302
  second_ne_zero : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
    0 < R.natDegree → ∀ z ∈ S \ Bad R,
      biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0

/-- Staged selection, arithmetic accounting, and pair setup in one theorem. -/
theorem exists_staged_pair_with_setup
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (G : StagedGoodFamily Q S)
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 255)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 63302)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 33398999)
    (hcard : 2 * 33398999 * 63302 * 255 ^ 2 +
      (bchksErrors + 1) * 255 + 2 * 63302 * 255 < S.card) :
    ∃ R H T,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R (G.x₀ R)) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ G.Bad R) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval (G.x₀ R) (P z)) z = 0) ∧
      2 * 33398999 * 63302 * R.natDegree * H.natDegree +
        (bchksErrors + 1) < T.card ∧
      Irreducible R ∧ Irreducible H ∧ H ∣ triSpecializeX R (G.x₀ R) ∧
      R.natDegree ≤ 255 ∧ H.natDegree ≤ 255 ∧
      Polynomial.Bivariate.totalDegree H ≤ 63302 ∧
      Polynomial.Bivariate.totalDegree (triSpecializeX R (G.x₀ R)) ≤ 63302 ∧
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 33398999) ∧
      RationalFunctions.HenselNumerators.Hypotheses (G.x₀ R) R H := by
  have hsum :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (2 * 33398999 * 63302 * R.natDegree ^ 2 +
          (bchksErrors + 1) * R.natDegree + G.badCap R)) ≤
        2 * 33398999 * 63302 * 255 ^ 2 +
          (bchksErrors + 1) * 255 + 2 * 63302 * 255 := by
    apply positive_normalizedFactors_staged_cap_le Q hQ G.badCap
      (2 * 33398999 * 63302) (bchksErrors + 1) 63302 255 hQY
    intro R hR
    have hm := Finset.mem_filter.mp hR
    exact G.bad_cap R (by simpa using hm.1) hm.2
  have hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (2 * 33398999 * 63302 * R.natDegree ^ 2 +
          (bchksErrors + 1) * R.natDegree + G.badCap R)) < S.card :=
    hsum.trans_lt hcard
  obtain ⟨R, H, T, hRQ, hRpos, hHR, hHpos, hTS, hTbad, hvan, hmargin⟩ :=
    exists_concrete_staged_factor_selection S P Q G.x₀ G.Bad G.badCap
      (2 * 33398999 * 63302) (bchksErrors + 1) hQ hQeval hQz
      G.specialize_ne_zero G.bad_card G.second_ne_zero hglobal
  have hp := bchks_pair_setup_of_selected_factors Q R H (G.x₀ R)
    hQ hRQ hHR hHpos hQY hQYZ hQweightedX (G.primitive R hRQ hRpos)
  rcases hp with ⟨hRirr, hHirr, -, hHd, hRdeg, hHdeg, hHtot, hRXtot, hweight, hHyp⟩
  exact ⟨R, H, T, hRQ, hRpos, hHR, hHpos, hTS, hTbad, hvan, hmargin,
    hRirr, hHirr, hHd, hRdeg, hHdeg, hHtot, hRXtot, hweight, hHyp⟩

end ProximityPrize.SubmissionLower
