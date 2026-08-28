import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTranslation6642FrozenResearch
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research

/-!
# Sharp factor caps from the score-66.42 flag-complete interpolant

The interpolant carries the direct cumulative bounds `R <= 8`,
`Y+R <= 40`, and `Y+R+Z <= 617`.  Weighted-degree additivity transfers
those bounds through product divisibility to the full family of positive-R
factors.  A separate compatibility lemma forgets the middle facet when a
legacy rectangular consumer only needs `Y+Z <= 617`.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6642Research

open scoped BigOperators
open ContactFlagInterpolation6642Research
open ContactFlagParameters6642Research
open ContactFactorCaps ContactGenericSurface
open ContactImplicitContactLift
open ContactCumulativeWeightedDegreeResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactRegularFactorFlag6630Research
open ContactSelectedSeedDecomposition

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]

/-- Forgetting the middle facet gives the legacy interpolation box with the
same weighted cap, total cap, and slope cap. -/
theorem flag_box_le_legacy_box
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q ∈ ContactFlagInterpolation6642Research.globalCoefficientBox K
      weightedCap w middleCap totalCap slopeCap) :
    Q ∈ ContactInterpolation.globalCoefficientBox K
      weightedCap w totalCap slopeCap := by
  intro d hd
  have h := hbox hd
  refine ⟨?_, h.2.2.1, h.2.2.2⟩
  exact (show d 1 + d 3 ≤ d 1 + d 2 + d 3 by omega).trans h.2.1

theorem residual_surface_weights_of_flag_box6642
    (Q : MvPolynomial (Fin 4) K)
    (hbox : Q ∈ ContactFlagInterpolation6642Research.globalCoefficientBox K
      weightedCap w middleCap totalCap slopeCap) :
    MvPolynomial.weightedTotalDegree residualSWeights Q ≤ slopeCap ∧
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ middleCap ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights Q ≤ totalCap := by
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights Q slopeCap).mpr
    intro d hd
    have h := hbox hd
    rw [weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ slopeCap
    norm_num
    exact h.2.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights Q middleCap).mpr
    intro d hd
    have h := hbox hd
    rw [weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ middleCap
    norm_num
    exact h.1
  · apply (weightedTotalDegree_le_iff residualTotalWeights Q totalCap).mpr
    intro d hd
    have h := hbox hd
    rw [weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ totalCap
    norm_num
    exact h.2.1

/-- Product divisibility transfers the three cumulative caps to all actual
positive-R factors without rectangular overcount. -/
theorem regularFlag6630_budgets_of_flag_box6642
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ ContactFlagInterpolation6642Research.globalCoefficientBox K
      weightedCap w middleCap totalCap slopeCap) :
    (∑ F : RegularIndex Q, (regularFlag6630 Q F).all) ≤ slopeCap ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).yz + (regularFlag6630 Q F).all)) ≤ middleCap ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).zOnly + (regularFlag6630 Q F).yz +
          (regularFlag6630 Q F).all)) ≤ totalCap := by
  classical
  have hprod := positiveRFactors_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hprod
  have hys := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hprod
  have htotal := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hprod
  obtain ⟨hQs, hQys, hQtotal⟩ :=
    residual_surface_weights_of_flag_box6642 Q hbox
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun F _ ↦
        (regularFlag6630_cumulative Q F).1), Finset.sum_coe_sort]
    exact hs.trans hQs
  · rw [Finset.sum_congr rfl (fun F _ ↦
        (regularFlag6630_cumulative Q F).2.1), Finset.sum_coe_sort]
    exact hys.trans hQys
  · rw [Finset.sum_congr rfl (fun F _ ↦
        (regularFlag6630_cumulative Q F).2.2), Finset.sum_coe_sort]
    exact htotal.trans hQtotal

end


end ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6642Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6642Research.flag_box_le_legacy_box
#print axioms ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6642Research.residual_surface_weights_of_flag_box6642
#print axioms ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6642Research.regularFlag6630_budgets_of_flag_box6642
