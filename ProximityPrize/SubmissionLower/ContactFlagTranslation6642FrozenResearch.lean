import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTranslation6642Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6642FrozenResearch

/-!
# Universal flag-complete vanishing interpolant at score 66.42

The explicit translated coefficient identities turn the frozen order-29
contact equations into specialization vanishing for every degree-`w`
polynomial agreeing on at least `agreements = 182950` coordinates.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch

open ProximityPrize.Benchmark
open ContactFlagRankKernel6642Research
open ContactFlagInterpolation6642Research
open ContactFlagInterpolation6642FrozenResearch
open ContactFlagTranslation6642Research
open ContactFlagParameters6642Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

theorem exists_frozen_translated_contact_interpolant6642
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w middleCap totalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (multiplicity - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u0 i) (u1 i) Q).coeff r := by
  obtain ⟨Q, theta, hQ, hcaps, hreconstruct, hequations⟩ :=
    exists_frozen_nonzero_polynomial_and_equations6642 u0 u1
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro i r
  rw [hreconstruct,
    translation_reconstruct_coeff IRSProfile.Field weightedCap w middleCap
      totalCap slopeCap]
  exact all_blocks_divisible_of_equations IRSProfile.Field
    weightedCap w middleCap totalCap slopeCap multiplicity
    (IRSProfile.domain i) (u0 i) (u1 i) theta (hequations i) r

theorem exists_frozen_universal_vanishing_interpolant6642
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w middleCap totalCap slopeCap ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hcontact⟩ :=
    exists_frozen_translated_contact_interpolant6642 u0 u1
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro gamma P support hP hcard hvalues
  apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P
    gamma IRSProfile.domain u0 u1 support multiplicity
  · intro i hi r
    exact hcontact i r
  · exact hvalues
  · have hdegree := specialization_natDegree_lt IRSProfile.Field
      weightedCap w middleCap totalCap slopeCap Q P gamma
      (by norm_num [ContactFlagParameters6642Research.weightedCap,
        ContactFlagParameters6642Research.multiplicity,
        ContactFlagParameters6642Research.agreements,
        ContactFlagParameters6642Research.n,
        ContactFlagParameters6642Research.errors])
      hcaps hP
    have hbound : ContactFlagParameters6642Research.weightedCap ≤
        ContactFlagParameters6642Research.multiplicity * support.card := by
      rw [ContactFlagParameters6642Research.weightedCap]
      exact Nat.mul_le_mul_left
        ContactFlagParameters6642Research.multiplicity hcard
    exact hdegree.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch

#print axioms ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch.exists_frozen_translated_contact_interpolant6642
#print axioms ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch.exists_frozen_universal_vanishing_interpolant6642
