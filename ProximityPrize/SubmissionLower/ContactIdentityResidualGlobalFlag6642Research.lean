import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactJointTaylorMiddleCap6631Research

/-!
# Sharp global residual flag for the score-66.42 row

This module freezes the cumulative surface caps

`R <= 8`, `Y + R <= 40`, `Y + R + Z <= 617`

and uses the equal-weight Taylor theorem for the last two facets.  The
agreement direction is therefore `(1154,63,15)`, rather than the generic
Minkowski direction `(1154,64,15)`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research

open scoped Classical BigOperators
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactPost6464ShearSupportResearch
open ContactJointTaylorMiddleCap6631Research
open ContactFlagBezout6543Research
open ContactGenericSurface ContactTaylorNumerators

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

def surfaceFlag6642 : FlagDegree := ⟨577, 32, 8⟩
def agreementDirection6642 : FlagDegree := ⟨1154, 63, 15⟩

def residualAgreementFlag6642 (d : ℕ) : FlagDegree :=
  unitYZFlag + d • agreementDirection6642

theorem residualAgreementFlag6642_value (d : ℕ) :
    residualAgreementFlag6642 d = ⟨1154 * d, 1 + 63 * d, 15 * d⟩ := by
  change (⟨0 + d * 1154, 1 + d * 63, 0 + d * 15⟩ : FlagDegree) =
    ⟨1154 * d, 1 + 63 * d, 15 * d⟩
  congr 1 <;> omega

/-- The target cumulative flag is invariant under every nodal residual
coordinate change. -/
theorem globalResidualHom_surface_flag_weights6642
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617) :
    wt residualSWeights (globalResidualHom P0 P1 V F) ≤ 8 ∧
      wt residualYSWeights (globalResidualHom P0 P1 V F) ≤ 40 ∧
      wt residualTotalWeights (globalResidualHom P0 P1 V F) ≤ 617 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_s] using hS)
  · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_ys] using hYS)
  · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_total] using hTotal)

/-- Agreement-cut cumulative bounds with both equal-weight facet savings. -/
theorem globalResidual_agreement_weight_bounds6642
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
          d coeffs x u0 u1) ≤ 1 + 1232 * d := by
  let Fres := globalResidualHom P0 P1 V F
  obtain ⟨hFs, hFys, hFtot⟩ :=
    globalResidualHom_surface_flag_weights6642 P0 P1 V F hS hYS hTotal
  have hR : Fres.degreeOf (2 : Fin 4) ≤ 8 := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hFs
    exact hFs
  have hY : Fres.degreeOf (1 : Fin 4) ≤ 40 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw :=
      (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans hFys
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ 40 at hw
    norm_num at hw
    omega
  have hZ : Fres.degreeOf (3 : Fin 4) ≤ 617 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw :=
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hFtot
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ 617 at hw
    norm_num at hw
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hr := (agreementNumerator_degree_bounds Fres 40 8 617
      (by norm_num) hY hR hZ d coeffs x u0 u1).2.1
    convert hr using 1 <;> ring
  · have h := agreementNumerator_wt_le_equal_weight residualYSWeights rfl
      Fres 40 (by change 1 ≤ 1; norm_num)
      (by change 1 ≤ 40; norm_num) (by change 2 * 1 ≤ 40; norm_num)
      (by change 1 ≤ 1; norm_num) hFys d coeffs x u0 u1
    calc
      wt residualYSWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          max (residualYSWeights 1) (residualYSWeights 3) +
            d * (2 * (40 - residualYSWeights 2)) := h
      _ = 1 + 78 * d := by
        change max 1 0 + d * (2 * (40 - 1)) = 1 + 78 * d
        norm_num
        ring
  · have h := agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
      Fres 617 (by change 1 ≤ 1; norm_num)
      (by change 1 ≤ 617; norm_num) (by change 2 * 1 ≤ 617; norm_num)
      (by change 1 ≤ 1; norm_num) hFtot d coeffs x u0 u1
    calc
      wt residualTotalWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          max (residualTotalWeights 1) (residualTotalWeights 3) +
            d * (2 * (617 - residualTotalWeights 2)) := h
      _ = 1 + 1232 * d := by
        change max 1 1 + d * (2 * (617 - 1)) = 1 + 1232 * d
        norm_num
        ring

/-- The mapped agreement polynomial lies in the sharp score-66.42 flag. -/
theorem surfaceMap_globalResidual_agreement_in_flag6642
    (phi : Polynomial K →+* Omega)
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag6642 d)
      (surfaceMap phi
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi
      (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1) he)
  obtain ⟨hR, hYS', hTot⟩ := globalResidual_agreement_weight_bounds6642
    P0 P1 V F hS hYS hTotal d coeffs x u0 u1
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS :=
    (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS'
  have hqTot :=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTot
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTot
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ 1 + 78 * d at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ 1 + 1232 * d at hqTot
  norm_num at hqYS hqTot
  rw [residualAgreementFlag6642_value]
  change q 2 ≤ 15 * d ∧
    q 1 + q 2 ≤ (1 + 63 * d) + 15 * d ∧
    q 1 + q 2 + q 3 ≤ 1154 * d + (1 + 63 * d) + 15 * d
  omega

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research.globalResidualHom_surface_flag_weights6642
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research.globalResidual_agreement_weight_bounds6642
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6642Research.surfaceMap_globalResidual_agreement_in_flag6642
