import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionLower.BCHKSInterpolation6399
import ProximityPrize.SubmissionLower.BCHKSQBadRemoval6399
import ProximityPrize.SubmissionLower.BCHKSSelectedFinal6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def BCHKSPolynomialAlignment6399 : Prop :=
  ∀ (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field) (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : ↥S → Polynomial IRSProfile.Field)
    (Q : Polynomial (Polynomial (Polynomial IRSProfile.Field))),
    bchksNumerator < S.card → Q ≠ 0 →
    (∀ z : ↥S, (P z).natDegree ≤ 131071) →
    (∀ z : ↥S, 185374 ≤ (A z.1).card) →
    (∀ z : ↥S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z.1 * U 1 i) →
    (∀ z : ↥S, triEval Q z.1 (P z) = 0) →
    (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      j < 5280 ∧ a + 131071 * j < 692001142 ∧
        ((Q.coeff j).coeff a).natDegree + j < 13141403) →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field, ∃ T : Finset IRSProfile.Field,
      ∃ hTS : T ⊆ S, 76770 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTS hz⟩ = p₀ + Polynomial.C z * p₁

private lemma degree_lt_baseDimension_of_natDegree_le_6399
    {p : Polynomial IRSProfile.Field} (hp : p.natDegree ≤ 131071) :
    p.degree < (IRSProfile.baseDimension : WithBot Nat) := by
  by_cases hzero : p = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [IRSProfile.baseDimension]
    omega

theorem alignmentBound_of_polynomialAlignment_6399
    (halg : BCHKSPolynomialAlignment6399) :
    AffineLineAlignmentBound IRSProfile.baseCode 76770 bchksNumerator := by
  classical
  intro U S A hS hA hcomb
  have hA' : ∀ z ∈ S, 185374 ≤ (A z).card := by
    intro z hz
    have h := hA z hz
    norm_num [IRSProfile.Index] at h
    exact h
  obtain ⟨P, Q, hQ, hPdeg, hPagree, hQvan, hcaps⟩ :=
    exists_bchks_interpolant_vanishing_6399 U S A hA' hcomb
  obtain ⟨p₀, p₁, T, hTS, hTcard, hp₀deg, hp₁deg, hline⟩ :=
    halg U S A P Q hS hQ hPdeg (fun z => hA' z z.property) hPagree hQvan hcaps
  let p : Fin 2 → IRSProfile.Index → IRSProfile.Field := fun j =>
    ReedSolomon.evalOnPoints IRSProfile.domain (if j = 0 then p₀ else p₁)
  refine ⟨p, ?_, T, hTS, hTcard, ?_⟩
  · intro j
    change p j ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    fin_cases j
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le_6399 hp₀deg
    · simpa [p] using degree_lt_baseDimension_of_natDegree_le_6399 hp₁deg
  · intro z hz x hx
    have hagree := hPagree ⟨z, hTS hz⟩ x hx
    have hpoly := congrArg (Polynomial.eval (IRSProfile.domain x)) (hline z hz)
    simp [p, ReedSolomon.evalOnPoints] at hpoly
    rw [← hagree]
    simpa [p, ReedSolomon.evalOnPoints, mul_add, add_mul] using hpoly

theorem bchksPolynomialAlignment6399 : BCHKSPolynomialAlignment6399 := by
  classical
  intro U S A P Q hScard hQ hPdeg hAcard hagree hQeval hcaps
  let PE : IRSProfile.Field → IRSProfile.Field[X] := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  have hQY : Q.natDegree ≤ 5279 := by
    have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlc
    have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.mem_support_iff.mp ha
    have := (hcaps Q.natDegree a hca).1
    omega
  obtain ⟨Sgood, rfl, hSgoodS, hQz, hQevalgood, -, hlarge⟩ :=
    exists_bchks_Qbad_removal_6399 S PE Q hScard hQ
      (by intro z hz; simpa [PE, hz, BCHKSSubstitutionVanish.triEval, triEval,
        BCHKSSubstitutionVanish.specializeZ] using hQeval ⟨z, hz⟩)
      (fun j a ha => (hcaps j a ha).2.2)
  obtain ⟨R, H, T, x₀, Bad, hRQ, hRpos, hHT, hHpos, hTS, hTbad,
      hvan, hmargin, hRi, hHi, -, -, -, hHtot, -, -, hHyp, -, hsimple⟩ :=
    bchks_staged_unconditional_6399 _ PE Q hQ hQevalgood hQz hQY
      (fun j a ha => (hcaps j a ha).2.2)
      (fun j a ha => (hcaps j a ha).2.1) hlarge
  have hPT : ∀ z ∈ T, (PE z).natDegree ≤ 131071 := by
    intro z hz
    have hzS : z ∈ S := hSgoodS (hTS hz)
    simpa [PE, hzS] using hPdeg ⟨z, hzS⟩
  have hrow : ∀ z ∈ T, 262144 - 76770 ≤ (A z).card := by
    intro z hz
    have hzS : z ∈ S := hSgoodS (hTS hz)
    norm_num
    exact hAcard ⟨z, hzS⟩
  have hagreeT : ∀ z ∈ T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (PE z) = U 0 i + z * U 1 i := by
    intro z hz i hi
    have hzS : z ∈ S := hSgoodS (hTS hz)
    simpa [PE, hzS] using hagree ⟨z, hzS⟩ i hi
  have hYZ : YZCap R 13141402 := by
    intro j a ha
    have hh := YZFactorCap.normalizedFactor_YZ_cap Q R 13141403 hQ hRQ
      (fun j a ha => (hcaps j a ha).2.2) j a ha
    omega
  obtain ⟨Tgood, hgoodT, hgoodcard, p₀, p₁, hp₀, hp₁, halign⟩ :=
    selected_pair_final_6399 U PE A R H T x₀ Bad hPT hvan hTbad hmargin
      hRi hRpos hHi hHpos hHyp hHtot hYZ hsimple hrow hagreeT
  refine ⟨p₀, p₁, Tgood, ?_, hgoodcard, hp₀, hp₁, ?_⟩
  · exact hgoodT.trans (hTS.trans hSgoodS)
  · intro z hz
    have hzS : z ∈ S := (hgoodT.trans (hTS.trans hSgoodS)) hz
    simpa [PE, hzS] using halign z hz

end ProximityPrize.SubmissionLower
