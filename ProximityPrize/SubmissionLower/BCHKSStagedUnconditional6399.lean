import ProximityPrize.SubmissionLower.BCHKSConcreteStagedPair
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffectiveResultant
import ProximityPrize.SubmissionLower.BCHKSFactorXDegree
import ProximityPrize.SubmissionLower.BCHKSStagedArithmetic
import ProximityPrize.SubmissionLower.BCHKSRawStaged6399
import ProximityPrize.SubmissionLower.BCHKSConcreteGS6399
import ProximityPrize.SubmissionLower.BCHKSPrimitiveEffectiveResultant6399

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- The concrete staged BCHKS selection, with all primitive-specialization
certificates constructed uniformly from the selected irreducible factor. -/
theorem bchks_staged_unconditional_6399
    (S : Finset ProximityPrize.Benchmark.IRSProfile.Field)
    (P : ProximityPrize.Benchmark.IRSProfile.Field →
      Polynomial ProximityPrize.Benchmark.IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)))
    (hQ : Q ≠ 0)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hQY : Q.natDegree ≤ 5279)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 13141403)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 692001142)
    (hS : 632746 * (2 * 5279 * 13141402) +
      (76770 + 1) * 5279 + 2 * 13141403 * 5279 < S.card) :
    ∃ R H T x₀, ∃ Bad : Finset ProximityPrize.Benchmark.IRSProfile.Field,
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
      (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
        a + 131071 * j < 692001142) ∧
      RationalFunctions.HenselNumerators.Hypotheses x₀ R H ∧
      Bad.card ≤ 2 * R.natDegree * 13141403 ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  let cert : ∀ R : Polynomial (Polynomial (Polynomial
      ProximityPrize.Benchmark.IRSProfile.Field)),
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q → 0 < R.natDegree →
      EffectivePrimitiveObstruction ProximityPrize.Benchmark.IRSProfile.Field R := by
    intro R hRQ hp
    have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ hQYZ
    have hRW := WeightedFactorCaps.coeff_cap_of_dvd Q R 131071 692001142 hQ
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQweightedX
    have hZ : ∀ j, (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤
        BCHKSConcreteGS6399.DZ := by
      intro j
      rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
        Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro a ha
      have hne : ((R.coeff j).coeff a) ≠ 0 := Polynomial.mem_support_iff.mp ha
      have := hRYZ j a hne
      norm_num [BCHKSConcreteGS6399.DZ] at *
      omega
    have hX : ∀ j, Polynomial.Bivariate.degreeX
        (Polynomial.Bivariate.swap (R.coeff j)) ≤ BCHKSConcreteGS6399.DX := by
      intro j
      rw [Polynomial.Bivariate.degreeX_swap]
      change (R.coeff j).natDegree ≤ BCHKSConcreteGS6399.DX
      by_cases hz : R.coeff j = 0
      · simp [hz]
      · have hl := Polynomial.leadingCoeff_ne_zero.mpr hz
        have hw := hRW j (R.coeff j).natDegree (by
          rw [Polynomial.coeff_natDegree]
          exact hl)
        norm_num [BCHKSConcreteGS6399.DX] at *
        omega
    exact Classical.choose
      (effectivePrimitiveObstruction_of_irreducible_6399 R
        (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible
        hp hZ hX)
  have hcertBound : ∀ R (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
      (hp : 0 < R.natDegree),
      (cert R hRQ hp).obstruction.natDegree ≤
        2 * (BCHKSConcreteGS6399.DZ + 1) * BCHKSConcreteGS6399.DX := by
    intro R hRQ hp
    exact Classical.choose_spec
      (effectivePrimitiveObstruction_of_irreducible_6399 R
        (UniqueFactorizationMonoid.prime_of_normalized_factor R hRQ).irreducible hp
        (by
          intro j
          have hcap := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ hQYZ
          rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
            Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
            Polynomial.Bivariate.natDegreeY_swap]
          unfold Polynomial.Bivariate.degreeX
          apply Finset.sup_le
          intro a ha
          have := hcap j a (Polynomial.mem_support_iff.mp ha)
          norm_num [BCHKSConcreteGS6399.DZ] at *
          omega)
        (by
          intro j
          rw [Polynomial.Bivariate.degreeX_swap]
          change (R.coeff j).natDegree ≤ BCHKSConcreteGS6399.DX
          by_cases hz : R.coeff j = 0
          · simp [hz]
          · have hcap := WeightedFactorCaps.coeff_cap_of_dvd Q R 131071 692001142 hQ
              (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQweightedX
            have := hcap j (R.coeff j).natDegree (by
              rw [Polynomial.coeff_natDegree]
              exact Polynomial.leadingCoeff_ne_zero.mpr hz)
            norm_num [BCHKSConcreteGS6399.DX] at *
            omega))
  apply exists_concrete_raw_staged_pair_6399 S P Q cert
  · intro R hRQ hp
    have hRd : R.natDegree ≤ 5280 := by
      calc
        R.natDegree ≤ ∑ A ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
            A.natDegree := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simpa using hRQ)
        _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
        _ ≤ 5280 := hQY.trans (by omega)
    have hfx : (factorXObstruction R).natDegree ≤
        (2 * R.natDegree + 2) * BCHKSConcreteGS6399.DX := by
      apply factorXObstruction_natDegree_le R BCHKSConcreteGS6399.DX
      · unfold Polynomial.Bivariate.degreeX
        apply Finset.sup_le
        intro j hj
        simp only [mapZToRatFunc, Polynomial.coeff_map]
        exact Polynomial.natDegree_map_le.trans (by
          have hc := WeightedFactorCaps.coeff_cap_of_dvd Q R 131071 692001142 hQ
            (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQweightedX
          by_cases hz : R.coeff j = 0
          · simp [hz]
          · have := hc j (R.coeff j).natDegree (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hz)
            norm_num [BCHKSConcreteGS6399.DX] at *
            omega)
      · by_cases hz : R.leadingCoeff = 0
        · simp [hz]
        · have hc := WeightedFactorCaps.coeff_cap_of_dvd Q R 131071 692001142 hQ
            (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ) hQweightedX
          have := hc R.natDegree R.leadingCoeff.natDegree (by
            rw [Polynomial.coeff_natDegree]
            exact Polynomial.leadingCoeff_ne_zero.mpr hz)
          norm_num [BCHKSConcreteGS6399.DX] at *
          omega
    have hb := hcertBound R hRQ hp
    calc
      (cert R hRQ hp).obstruction.natDegree + (factorXObstruction R).natDegree ≤
          2 * (BCHKSConcreteGS6399.DZ + 1) * BCHKSConcreteGS6399.DX +
            (2 * 5280 + 2) * BCHKSConcreteGS6399.DX := by
        exact Nat.add_le_add hb (hfx.trans (Nat.mul_le_mul_right BCHKSConcreteGS6399.DX (by omega)))
      _ < Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := by
        rw [CompPoly.Extension.Ext.card_ext]
        norm_num [BCHKSConcreteGS6399.DZ, BCHKSConcreteGS6399.DX, KoalaBear.fieldSize]
  · intro R hRQ hp x
    have hRYZ := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ hQYZ
    have hcoeffCap : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤ 13141403 := by
      intro j
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro a ha
      have := hRYZ j a (Polynomial.mem_support_iff.mp ha)
      omega
    have hevalCap : ∀ p : Polynomial (Polynomial
        ProximityPrize.Benchmark.IRSProfile.Field),
        Polynomial.Bivariate.degreeX p ≤ 13141403 →
        (Polynomial.eval (Polynomial.C x) p).natDegree ≤ 13141403 := by
      intro p hpdeg
      have heq : (Polynomial.Bivariate.swap p).map
          (Polynomial.evalRingHom x) = Polynomial.eval (Polynomial.C x) p := by
        rw [← Polynomial.Bivariate.evalX_eq_map]
        exact (Polynomial.Bivariate.evalY_eq_evalX_swap x p).symm
      rw [← heq]
      exact Polynomial.natDegree_map_le.trans (by
        rw [show (Polynomial.Bivariate.swap p).natDegree =
          Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap p) from rfl,
          Polynomial.Bivariate.natDegreeY_swap]
        exact hpdeg)
    apply factorXObstruction_eval_natDegree_le R x R.natDegree 13141403 hp (le_refl _)
    · unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro j hj
      simp only [triSpecializeX, Polynomial.coeff_map]
      exact hevalCap (R.coeff j) (hcoeffCap j)
    · exact hevalCap R.leadingCoeff (by
        rw [← Polynomial.coeff_natDegree]
        exact hcoeffCap R.natDegree)
  · let E := ProximityPrize.Benchmark.IRSProfile.Field
    let K := KoalaBear.Field
    have hinj := FaithfulSMul.algebraMap_injective K E
    have hne := CharP.ringChar_ne_zero_of_finite E
    by_contra hn
    have hle : ringChar E ≤ 5280 := Nat.le_of_not_gt hn
    have hzE : ((ringChar E : ℕ) : E) = 0 := CharP.cast_eq_zero E _
    have hzK : ((ringChar E : ℕ) : K) = 0 := by
      apply hinj
      change ((ringChar E : ℕ) : E) = 0
      exact hzE
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hzK
    rcases hd with ⟨c, hc⟩
    have hc0 : c = 0 := by
      by_contra hcne
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hcne
      have hm := Nat.mul_le_mul_left KoalaBear.fieldSize hc1
      rw [← hc] at hm
      norm_num [KoalaBear.fieldSize] at hm hle
      omega
    exact hne (by rw [hc, hc0]; simp)
  · exact hQ
  · exact hQeval
  · exact hQz
  · exact hQY
  · exact hQYZ
  · exact hQweightedX
  · exact hS

end ProximityPrize.SubmissionLower
