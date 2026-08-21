import ProximityPrize.SubmissionLower.BCHKSRawHenselDegree
import ProximityPrize.SubmissionLower.BCHKSSecondStageCapacity6395
import ProximityPrize.SubmissionLower.BCHKSBaseZAffine
import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open RawHenselDegree

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The existing integral numerator is the reduced raw numerator times a
pure power of `W`.  That power is harmless on the selected non-pole fibers. -/
theorem embedding_explicitBaseZ_eq_raw_mul_W
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : Nat) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H
        (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k *
        Wfield (H := H) ^
          (k + 1 + (R.natDegree - 2) *
            FiniteHenselWeight.denominatorExponent k) := by
  rw [embedding_explicitBaseZGammaDifferenceRegular]
  unfold commonDenominator rawBaseZGammaDifference
  rw [etaField_eq]
  rw [mul_pow, ← pow_mul]
  rw [show Wfield (H := H) ^ (k + 1) *
        (Wfield (H := H) ^ ((R.natDegree - 2) *
            FiniteHenselWeight.denominatorExponent k) *
          RationalFunctions.HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent k) =
      (Wfield (H := H) ^ (k + 1) *
        Wfield (H := H) ^ ((R.natDegree - 2) *
          FiniteHenselWeight.denominatorExponent k)) *
        RationalFunctions.HenselNumerators.zeta R x₀ H ^
          FiniteHenselWeight.denominatorExponent k by ring]
  rw [← pow_add]
  ring

/-- A chosen raw polynomial representative vanishes at every selected pair
where the old integral numerator vanishes and `W(z)` is nonzero. -/
theorem evalEval_rawBaseZ_rep_eq_zero
    (x₀ dx u₀ u₁ z y : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : Nat) (hkN : k ≤ N)
    (B : F[X][Y])
    (hB : rawLiftHom (H := H) B =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k)
    (root : rationalRoot (monicize H) z)
    (hy : GoodAt z root (initialValue (H := H)) y)
    (hW : H.leadingCoeff.eval z ≠ 0)
    (hpi : piZ z root
      (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0) :
    Polynomial.evalEval z y B = 0 := by
  let old := explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN
  let s := k + 1 + (R.natDegree - 2) * FiniteHenselWeight.denominatorExponent k
  have hraw := GoodAt.rawLiftHom (H := H) B hy
  rw [hB] at hraw
  have hWgood := GoodAt.liftToFunctionField (H := H) z root H.leadingCoeff
  have hprod := GoodAt.mul hraw (GoodAt.pow hWgood s)
  have hold : embeddingOf𝒪Into𝕃 H old =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k *
        Wfield (H := H) ^ s := by
    simpa [old, s] using embedding_explicitBaseZ_eq_raw_mul_W
      (H := H) x₀ dx u₀ u₁ R hHyp hzeta N k hkN
  have hprod' : GoodAt z root (embeddingOf𝒪Into𝕃 H old)
      (Polynomial.evalEval z y B * (H.leadingCoeff.eval z) ^ s) := by
    rw [hold]
    simpa [Wfield] using hprod
  have hzero : GoodAt z root (embeddingOf𝒪Into𝕃 H old) 0 := by
    refine ⟨old, 1, ?_, by simp, ?_⟩
    · simp
    · simpa using hpi.symm
  have hv := GoodAt.value_unique hprod' hzero
  have hpow : (H.leadingCoeff.eval z) ^ s ≠ 0 := pow_ne_zero _ hW
  exact (mul_eq_zero.mp hv).resolve_right hpow

/-- The reduced gamma representative is divisible by the raw specialization
factor once a fiber exceeds its exact bidegree resultant cost. -/
theorem rawBaseZGamma_dvd_of_many_pairs
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : Nat) (hkN : k ≤ N)
    (B : F[X][Y])
    (hB : rawLiftHom (H := H) B =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k)
    (S : Finset F) (y : F → F)
    (hHroot : ∀ z ∈ S, Polynomial.evalEval z (y z) H = 0)
    (root : ∀ z : {z // z ∈ S}, rationalRoot (monicize H) (z : F))
    (hy : ∀ z : {z // z ∈ S},
      GoodAt (z : F) (root z) (initialValue (H := H)) (y z))
    (hW : ∀ z : {z // z ∈ S}, H.leadingCoeff.eval (z : F) ≠ 0)
    (hpi : ∀ z : {z // z ∈ S},
      piZ (z : F) (root z)
        (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0)
    (hmany : H.natDegree * degreeX B + B.natDegree * degreeX H < S.card) :
    H ∣ B := by
  apply SecondStageCapacity.irreducible_dvd_of_many_bivariate_common_roots_primitive
    B H S y ((Fact.out : Irreducible H).isPrimitive
      (Nat.ne_of_gt (Fact.out : 0 < H.natDegree)))
    (Fact.out : Irreducible H) (Fact.out : 0 < H.natDegree) hmany
  intro z hz
  let zs : {z // z ∈ S} := ⟨z, hz⟩
  constructor
  · rw [Polynomial.map_evalRingHom_eval]
    exact evalEval_rawBaseZ_rep_eq_zero (H := H)
      x₀ dx u₀ u₁ z (y z) R hHyp hzeta N k hkN B hB
      (root zs) (hy zs) (hW zs) (hpi zs)
  · rw [Polynomial.map_evalRingHom_eval]
    exact hHroot z hz

theorem rawBaseZGamma_dvd_of_many_pairs_fintype
    {ι : Type*} [Fintype ι]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : Nat) (hkN : k ≤ N)
    (B : F[X][Y])
    (hB : rawLiftHom (H := H) B =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k)
    (z y : ι → F) (hzInj : Function.Injective z)
    (hHroot : ∀ i, Polynomial.evalEval (z i) (y i) H = 0)
    (root : ∀ i, rationalRoot (monicize H) (z i))
    (hy : ∀ i, GoodAt (z i) (root i) (initialValue (H := H)) (y i))
    (hW : ∀ i, H.leadingCoeff.eval (z i) ≠ 0)
    (hpi : ∀ i, piZ (z i) (root i)
      (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0)
    (hmany : H.natDegree * degreeX B + B.natDegree * degreeX H <
      Fintype.card ι) :
    H ∣ B := by
  apply SecondStageCapacity.irreducible_dvd_of_many_bivariate_common_roots_primitive_fintype
    B H z y hzInj ((Fact.out : Irreducible H).isPrimitive
      (Nat.ne_of_gt (Fact.out : 0 < H.natDegree)))
    (Fact.out : Irreducible H) (Fact.out : 0 < H.natDegree) hmany
  intro i
  constructor
  · rw [Polynomial.map_evalRingHom_eval]
    exact evalEval_rawBaseZ_rep_eq_zero (H := H)
      x₀ dx u₀ u₁ (z i) (y i) R hHyp hzeta N k hkN B hB
      (root i) (hy i) (hW i) (hpi i)
  · rw [Polynomial.map_evalRingHom_eval]
    exact hHroot i

theorem rawBaseZGamma_eq_zero_of_dvd
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y]) (N k : Nat)
    (B : F[X][Y])
    (hB : rawLiftHom (H := H) B =
      rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k)
    (hdvd : H ∣ B) :
    rawBaseZGammaDifference (H := H) x₀ dx u₀ u₁ R N k = 0 := by
  obtain ⟨C, rfl⟩ := hdvd
  rw [map_mul, RawHenselDegree.rawLiftHom_H_eq_zero, zero_mul] at hB
  exact hB.symm

/-- Final base-coordinate alignment using the raw bidegree resultant instead
of the monicized scalar weight. -/
theorem hensel_baseZ_alignment_final_raw
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (D k N : Nat) (hkN : k < N)
    (hYZ : YZCap R D) (hRpos : 0 < R.natDegree)
    (T : Finset F) (root : ∀ z : T, rationalRoot (monicize H) (z : F))
    (P : T → F[X]) (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hfactor : ∀ z : T, Polynomial.evalEval (z : F) ((P z).eval x₀) H = 0)
    (hx : ∀ z : T, GoodAt (z : F) (root z) (fieldTo𝕃 (H := H) x₀) x₀)
    (hy : ∀ z : T, GoodAt (z : F) (root z) (initialValue (H := H)) ((P z).eval x₀))
    (hsL : FiniteHensel.ySlope (liftedR (R := R) (H := H))
      (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)) ≠ 0)
    (hsimple : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀))
    (hExact : ∀ z : T, (triSpecializeZ R (z : F)).eval (P z) = 0)
    (hslope : ∀ z : T, GoodAt (z : F) (root z)
      (FiniteHensel.ySlope (liftedR (R := R) (H := H))
        (fieldTo𝕃 (H := H) x₀) (initialValue (H := H)))
      (FiniteHensel.ySlope (triSpecializeZ R (z : F)) x₀ ((P z).eval x₀)))
    (hW : ∀ z : T, H.leadingCoeff.eval (z : F) ≠ 0)
    (hxi : ∀ z : T, Polynomial.evalEval (z : F) (root z).1 (xiPre x₀ R H) ≠ 0)
    (hden : ∀ t, t < N → ∀ z : T,
      piZ (z : F) (root z) (concreteDenRegularBridge x₀ R hHyp t) ≠ 0)
    (hkF : k < Fintype.card F)
    (A : Finset F) (hAcard : k + 1 ≤ A.card) (U₀ U₁ : F → F)
    (Fib : A → Finset T)
    (hFibcard : ∀ x : A,
      H.natDegree * (FiniteHenselWeight.denominatorExponent k * D + 1) +
        (FiniteHenselWeight.denominatorExponent k * (R.natDegree - 1) + 1) *
          degreeX H < (Fib x).card)
    (hagree : ∀ x : A, ∀ z ∈ Fib x,
      (P z).eval (x : F) = U₀ x + (z : F) * U₁ x)
    (_hk : k = 131071) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : F) * p₁ := by
  have hspecializes : ∀ z : T, ∀ n, n ≤ N →
      concreteSpecializedAlpha x₀ R hHyp hzeta N (z : F) (root z) n =
        FiniteHensel.TaylorCoeff (P z) x₀ n := by
    intro z n hn
    apply concreteSpecializedAlpha_eq_TaylorCoeff x₀ R hHyp hzeta N
      (z : F) (root z) x₀ ((P z).eval x₀) (P z)
      (hx z) (hy z) hsL (hsimple z) rfl
      ((hPdeg z).trans (Nat.le_of_lt hkN)) (hExact z) (hslope z) (hW z)
      (hxi z) n hn
  let γ := canonicalFunctionFieldGamma H x₀ R N k
  have hγeval : ∀ x ∈ A, γ.eval (fieldTo𝕃 (H := H) x) =
      fieldTo𝕃 (H := H) (U₀ x) +
        liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) (U₁ x) := by
    intro x hxA
    let rawγ := rawBaseZGammaDifference (H := H)
      x₀ (x - x₀) (U₀ x) (U₁ x) R N k
    obtain ⟨B, hB, hBY, hBZ⟩ := rawBaseZGammaDifference_bidegree (H := H)
      x₀ (x - x₀) (U₀ x) (U₁ x) R D N k hYZ hRpos hzeta
      (Nat.le_of_lt hkN)
    let ι := {z // z ∈ Fib ⟨x, hxA⟩}
    let zf : ι → F := fun z => (z.1 : F)
    let yf : ι → F := fun z => (P z.1).eval x₀
    let rf : ∀ z : ι, rationalRoot (monicize H) (zf z) := fun z => root z.1
    have hzInj : Function.Injective zf := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact hab
    have hpi : ∀ z : ι, piZ (zf z) (rf z)
        (explicitBaseZGammaDifferenceRegular x₀ (x - x₀) (U₀ x) (U₁ x)
          R hHyp hzeta N k (Nat.le_of_lt hkN)) = 0 := by
      intro z
      rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
        x₀ (x - x₀) (U₀ x) (U₁ x) (zf z) (rf z)
        R hHyp hzeta N k (Nat.le_of_lt hkN) (P z.1) (hPdeg z.1)]
      · simpa [zf, sub_eq_add_neg, add_assoc] using hagree ⟨x, hxA⟩ z.1 z.2
      · intro i hi
        exact hspecializes z.1 i (hi.trans (Nat.le_of_lt hkN))
      · intro i hi
        exact hden i (hi.trans_lt hkN) z.1
    have hresCost : H.natDegree * degreeX B + B.natDegree * degreeX H <
        Fintype.card ι := by
      have hle : H.natDegree * degreeX B + B.natDegree * degreeX H ≤
          H.natDegree *
              (FiniteHenselWeight.denominatorExponent k * D + 1) +
            (FiniteHenselWeight.denominatorExponent k * (R.natDegree - 1) + 1) *
              degreeX H := Nat.add_le_add
        (Nat.mul_le_mul_left H.natDegree hBZ)
        (Nat.mul_le_mul_right (degreeX H) hBY)
      have hcard := hFibcard ⟨x, hxA⟩
      rw [Fintype.card_coe]
      exact hle.trans_lt hcard
    have hdvd : H ∣ B := rawBaseZGamma_dvd_of_many_pairs_fintype (H := H)
      x₀ (x - x₀) (U₀ x) (U₁ x) R hHyp hzeta N k (Nat.le_of_lt hkN)
      B hB zf yf hzInj (fun z => hfactor z.1) rf
      (fun z => hy z.1) (fun z => hW z.1) hpi hresCost
    have hraw0 : rawγ = 0 := by
      exact rawBaseZGamma_eq_zero_of_dvd (H := H)
        x₀ (x - x₀) (U₀ x) (U₁ x) R N k B hB hdvd
    have hζpow :
        (RationalFunctions.HenselNumerators.zeta R x₀ H) ^
          FiniteHenselWeight.denominatorExponent k ≠ 0 := pow_ne_zero _ hzeta
    have hdiff : evaluatedFiniteAlpha (R := R) (H := H) x₀ (x - x₀) N k =
        fieldTo𝕃 (H := H) (U₀ x) +
          liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) (U₁ x) := by
      unfold rawγ rawBaseZGammaDifference at hraw0
      exact sub_eq_zero.mp ((mul_eq_zero.mp hraw0).resolve_right hζpow)
    rw [canonicalFunctionFieldGamma_eval]
    exact hdiff
  obtain ⟨p₀, p₁, hp₀, hp₁, hγ⟩ :=
    canonicalFunctionFieldGamma_baseZ_affine x₀ R N k A hAcard U₀ U₁
      (canonicalFunctionFieldGamma_natDegree_le x₀ R N k) hγeval
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  intro z
  let q := p₀ + Polynomial.C (z : F) * p₁
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P z) q
    (f := fun x : F => x) Function.injective_id
  · intro x
    have hall : γ.eval (fieldTo𝕃 (H := H) x) =
        fieldTo𝕃 (H := H) (p₀.eval x) +
          liftToFunctionField (H := H) Polynomial.X *
            fieldTo𝕃 (H := H) (p₁.eval x) := by
      change (canonicalFunctionFieldGamma H x₀ R N k).eval
        (fieldTo𝕃 (H := H) x) = _
      rw [hγ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map]
      have hp0map : Polynomial.eval₂
          (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₀ =
          liftToFunctionField (H := H) (Polynomial.C (p₀.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₀ Polynomial.C (liftToFunctionField (H := H))
          (Polynomial.C x)]
        simp
      have hp1map : Polynomial.eval₂
          (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₁ =
          liftToFunctionField (H := H) (Polynomial.C (p₁.eval x)) := by
        rw [← Polynomial.hom_eval₂ p₁ Polynomial.C (liftToFunctionField (H := H))
          (Polynomial.C x)]
        simp
      change Polynomial.eval₂ (liftToFunctionField (H := H) |>.comp Polynomial.C)
          (liftToFunctionField (H := H) (Polynomial.C x)) p₀ +
        liftToFunctionField (H := H) Polynomial.X *
          Polynomial.eval₂ (liftToFunctionField (H := H) |>.comp Polynomial.C)
            (liftToFunctionField (H := H) (Polynomial.C x)) p₁ = _
      rw [hp0map, hp1map]
      rfl
    let β := explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
      (p₀.eval x) (p₁.eval x) R hHyp hzeta N k (Nat.le_of_lt hkN)
    have hb0 : embeddingOf𝒪Into𝕃 H β = 0 := by
      rw [embedding_explicitBaseZGammaDifferenceRegular x₀ (x - x₀)
        (p₀.eval x) (p₁.eval x) R hHyp hzeta N k (Nat.le_of_lt hkN)]
      change (canonicalFunctionFieldGamma H x₀ R N k).eval
        (fieldTo𝕃 (H := H) x) = _ at hall
      rw [canonicalFunctionFieldGamma_eval] at hall
      rw [hall]
      ring
    have hβzero : β = 0 := by
      apply embeddingOf𝒪Into𝕃_injective (Fact.out : 0 < H.natDegree)
      simpa using hb0
    have hpiz : piZ (z : F) (root z) β = 0 := by rw [hβzero]; simp
    rw [piZ_explicitBaseZGammaDifferenceRegular_eq_zero_iff
      x₀ (x - x₀) (p₀.eval x) (p₁.eval x) (z : F) (root z)
      R hHyp hzeta N k (Nat.le_of_lt hkN) (P z) (hPdeg z)] at hpiz
    · simpa [q, sub_eq_add_neg, Polynomial.eval_add, Polynomial.eval_mul] using hpiz
    · intro i hi
      exact hspecializes z i (hi.trans (Nat.le_of_lt hkN))
    · intro i hi
      exact hden i (hi.trans_lt hkN) z
  · have hq : q.natDegree ≤ k :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le hp₀ ((Polynomial.natDegree_C_mul_le _ _).trans hp₁))
    exact max_lt ((hPdeg z).trans_lt hkF) (hq.trans_lt hkF)

end ProximityPrize.SubmissionLower
