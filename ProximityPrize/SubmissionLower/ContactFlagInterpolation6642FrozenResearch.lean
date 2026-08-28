import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6642Research
import ProximityPrize.SubmissionLower.ContactFlagParameters6642Research

/-!
# Frozen flag-complete contact interpolation for score 66.42

This instantiates the actual flag contact map at
`(D,M,L,s,m) = (5305550,40,617,8,29)`.  Its only numerical input is the
kernel-checked positive dimension margin from `ContactFlagParameters6642Research`.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagInterpolation6642FrozenResearch

open ProximityPrize.Benchmark
open ContactFlagRankKernel6642Research
open ContactFlagInterpolation6642Research
open ContactFlagParameters6642Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

abbrev FrozenCoefficientIndex6642 :=
  CoefficientIndex weightedCap w middleCap totalCap slopeCap

theorem exists_frozen_nonzero_contact_array6642
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ theta : FrozenCoefficientIndex6642 → IRSProfile.Field, theta ≠ 0 ∧
      ∀ (i : IRSProfile.Index) (r : Fin multiplicity),
        contactJet IRSProfile.Field (multiplicity - r.val)
          ((extractBlock IRSProfile.Field weightedCap w middleCap totalCap
            slopeCap (IRSProfile.domain i) (u0 i) (u1 i) r.val theta) :
              Poly IRSProfile.Field) = 0 := by
  apply exists_nonzero_block_equations IRSProfile.Field
    weightedCap w middleCap totalCap slopeCap multiplicity
    (fun i : IRSProfile.Index ↦ IRSProfile.domain i) u0 u1
  · norm_num [ContactFlagParameters6642Research.middleCap,
      ContactFlagParameters6642Research.weightedCap,
      ContactFlagParameters6642Research.multiplicity,
      ContactFlagParameters6642Research.agreements,
      ContactFlagParameters6642Research.n,
      ContactFlagParameters6642Research.errors,
      ContactFlagParameters6642Research.w,
      ContactFlagParameters6642Research.totalCap]
  · rw [show Fintype.card IRSProfile.Index = n by
      norm_num [IRSProfile.Index, n]]
    change n * localContactRank <
      ContactFlagParameters6642Research.coefficientCount
    exact interpolation_gate

theorem exists_frozen_nonzero_polynomial_and_equations6642
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ (Q : MvPolynomial (Fin 4) IRSProfile.Field)
      (theta : FrozenCoefficientIndex6642 → IRSProfile.Field),
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w middleCap totalCap slopeCap ∧
      Q = reconstruct IRSProfile.Field weightedCap w middleCap totalCap
        slopeCap theta ∧
      ∀ (i : IRSProfile.Index) (r : Fin multiplicity),
        contactJet IRSProfile.Field (multiplicity - r.val)
          ((extractBlock IRSProfile.Field weightedCap w middleCap totalCap
            slopeCap (IRSProfile.domain i) (u0 i) (u1 i) r.val theta) :
              Poly IRSProfile.Field) = 0 := by
  obtain ⟨theta, htheta, hconstraints⟩ :=
    exists_frozen_nonzero_contact_array6642 u0 u1
  exact ⟨reconstruct IRSProfile.Field weightedCap w middleCap totalCap
      slopeCap theta,
    theta,
    reconstruct_ne_zero IRSProfile.Field weightedCap w middleCap totalCap
      slopeCap theta htheta,
    reconstruct_mem_globalCoefficientBox IRSProfile.Field weightedCap w
      middleCap totalCap slopeCap theta,
    rfl, hconstraints⟩

end

end ProximityPrize.SubmissionLower.ContactFlagInterpolation6642FrozenResearch

#print axioms ProximityPrize.SubmissionLower.ContactFlagInterpolation6642FrozenResearch.exists_frozen_nonzero_contact_array6642
#print axioms ProximityPrize.SubmissionLower.ContactFlagInterpolation6642FrozenResearch.exists_frozen_nonzero_polynomial_and_equations6642
