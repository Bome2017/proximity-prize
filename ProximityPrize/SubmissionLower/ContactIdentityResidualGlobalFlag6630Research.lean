import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch

/-!
# Score-66.42 global residual flag adapter

The adaptive residual pipeline historically imports this namespace. These
aliases expose the independently proved score-66.42 cumulative caps
`R <= 8`, `Y+R <= 40`, `Y+R+Z <= 617` and the sharp agreement direction
`(1154,63,15)` through that stable interface.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualGlobalFlag6642Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactNearPencil6630FlagResearch
open ContactFlagBezout6543Research
open ContactGenericSurface ContactTaylorNumerators

noncomputable section

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

theorem globalResidualHom_surface_flag_weights6630
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617) :
    wt residualSWeights (globalResidualHom P0 P1 V F) ≤ 8 ∧
      wt residualYSWeights (globalResidualHom P0 P1 V F) ≤ 40 ∧
      wt residualTotalWeights (globalResidualHom P0 P1 V F) ≤ 617 :=
  globalResidualHom_surface_flag_weights6642 P0 P1 V F hS hYS hTotal

theorem globalResidual_agreement_weight_bounds6630
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1).degreeOf (2 : Fin 4) ≤ 15 * d ∧
      wt residualYSWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 78 * d ∧
      wt residualTotalWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 1232 * d :=
  globalResidual_agreement_weight_bounds6642 P0 P1 V F hS hYS hTotal
    d coeffs x u0 u1

theorem surfaceMap_globalResidual_agreement_in_flag6630
    (phi : Polynomial K →+* Omega)
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag6630 d)
      (surfaceMap phi
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1)) := by
  simpa [residualAgreementFlag6630, residualAgreementFlag6642,
    agreementDirection6630, agreementDirection6642] using
      surfaceMap_globalResidual_agreement_in_flag6642 phi P0 P1 V F
        hS hYS hTotal d coeffs x u0 u1

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.globalResidualHom_surface_flag_weights6630
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.globalResidual_agreement_weight_bounds6630
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.surfaceMap_globalResidual_agreement_in_flag6630
