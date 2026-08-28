import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTranslation
import ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch
import ProximityPrize.SubmissionLower.ContactParameters6630Research

/-!
# Flag-complete universal vanishing interpolant for score 66.42

This adapter exposes the independently checked flag-complete interpolant to
the established adaptive pipeline.  It records both the sharp nested support
and the weaker legacy box needed by unchanged singular-factor interfaces.
-/

namespace ProximityPrize.SubmissionLower.ContactTranslation6630Research

open ProximityPrize.Benchmark
open ContactParameters6630Research ContactTranslation
open ContactFlagRankKernel6642Research
open ContactFlagInterpolation6642Research
open ContactFlagTranslation6642Research
open ContactFlagTranslation6642FrozenResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

theorem flagCoefficientBox_le_rectangular (K : Type*) [Field K]
    (D w M L s : ℕ) :
    ContactFlagInterpolation6642Research.globalCoefficientBox K D w M L s ≤
      ContactInterpolation.globalCoefficientBox K D w L s := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  change d 1 + d 2 ≤ M ∧ d 1 + d 2 + d 3 ≤ L ∧ d 2 ≤ s ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D at hd
  change d 1 + d 3 ≤ L ∧ d 2 ≤ s ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D
  exact ⟨by omega, hd.2.2.1, hd.2.2.2⟩

theorem exists_frozen_universal_vanishing_interpolant6630
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      Q ∈ ContactFlagInterpolation6642Research.globalCoefficientBox
        IRSProfile.Field weightedCap w yCap seedTotalCap slopeCap ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        ContactTranslation.specialization IRSProfile.Field P gamma Q = 0 := by
  obtain ⟨Q, hQ, hsharp, hvanish⟩ :=
    exists_frozen_universal_vanishing_interpolant6642 u0 u1
  have hlegacy := flagCoefficientBox_le_rectangular IRSProfile.Field
    weightedCap w yCap seedTotalCap slopeCap hsharp
  refine ⟨Q, hQ, hlegacy, hsharp, ?_⟩
  intro gamma P support hP hcard hvalues
  have h := hvanish gamma P support hP hcard hvalues
  exact h

end

end ProximityPrize.SubmissionLower.ContactTranslation6630Research

#print axioms ProximityPrize.SubmissionLower.ContactTranslation6630Research.exists_frozen_universal_vanishing_interpolant6630
