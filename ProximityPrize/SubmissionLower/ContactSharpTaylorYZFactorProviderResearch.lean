import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactProfileYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch

/-!
# Sharp equal-weight Taylor flags with the active Z/YZ factor provider

This module supplies the missing direction seam between the equal-weight
Taylor support theorem and the profile-generic active-YZ component provider.
It keeps the stored residual support used by the recursive coordinate changes,
but indexes every agreement cut by the smaller sharp flag.
-/

namespace ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch

open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualCoordinateDegreeSum
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactIncidence
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactIdentityResidualCurveTerminalIncidenceResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactIdentityResidualComponentFamilyYZSupportResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactIdentityResidualFactorProvider6600Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorFixedMeet6656Research
open ContactProfileYZFactorLedgerResearch
open ContactTerminalAdaptiveProjectionFixedMeetActive6656Research
open ContactNearPencilStratifiedIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactResidualSparseComponentAdapterResearch
open ContactStratifiedResidualComponentAdapter6600Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveNestedYZFamily6630Research
open ContactWeakSeparableSeparatorResearch
open ContactScalarCoordinateSeparator6630Research
open ContactResidualStageDerivative6600Research
open ContactTerminalAdaptiveProjection6656Research
open ContactCongruentCuts6643Research ContactReducedTaylorProfileResearch

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Prime-budget recursive incidence with a caller-supplied flag for every
terminal agreement degree.  This is the narrow parameterization of the
accepted recursive theorem needed by equal-weight Taylor cuts. -/
theorem recursive_curve_stratified_incidence_of_prime_flag_budget_for_cuts
    {e d a : ℕ} {surfaceFlag cutFlag : FlagDegree}
    {support : ResidualSupportParameters}
    (hphi : Function.Injective phi)
    (S : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag d support)
    (cutAt : ℕ → FlagDegree) (cost : FlagDegree → ℕ)
    (B : PrimeFlagZeroBudget S.primeIdeal cost)
    (degreeCost unitCost U V zCharge : ℕ)
    (hcost : ∀ t : ℕ, cost (cutAt t) = t * degreeCost + unitCost)
    (hcut : ∀ D : S.TerminalDescendant, D.stage.identities = ∅ →
      ∀ i ∈ D.stage.nodes,
        PolynomialInFlagMod D.stage.primeIdeal (cutAt D.degree)
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i)))
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma, a ≤ (S.agreementFiber gamma).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  classical
  let Inv : ∀ n, CurveResidualStage phi Gamma x pchar e
      surfaceFlag cutFlag n support → Prop :=
    fun _ A ↦ PrimeFlagZeroBudget A.primeIdeal cost
  have htransport : ∀ {n m}
      {A : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag n support}
      {Anext : CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag m support},
      A.ResidualTransition Anext → Inv n A → Inv m Anext := by
    intro n m A Anext htransition hbudget
    obtain ⟨aY, v, bY, aS, bS, cS, hv, _, _, hprime⟩ := htransition
    dsimp only [Inv] at hbudget ⊢
    rw [hprime]
    exact hbudget.mapResidual aY v bY aS bS cS hv
  obtain ⟨D, hDBudget⟩ := S.exists_terminal_descendant_with_invariant
    hphi Inv htransport B
  rcases D.terminal with hproper | hpencil
  · let k := d - D.degree
    have hk : k ≤ d := Nat.sub_le d D.degree
    have hDle : D.degree ≤ d := D.degree_le
    have hdegreeEq : D.degree = d - k := by
      dsimp only [k]
      omega
    have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
      simpa only [k] using D.nodes_card
    have hterminalAgreement : ∀ gamma ∈ Gamma,
        a - k ≤ (D.stage.agreementFiber gamma).card := by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber : ∀ i ∈ D.stage.nodes,
        (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost := by
      intro i hi
      have hflag := hcut D hproper i hi
      have hzero :=
        ContactCongruentCuts6643Research.PrimeFlagZeroBudget.zero_le_congr
          hDBudget (cutAt D.degree)
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        hflag (D.stage.proper_agreement_of_terminal hproper hi)
      rw [hcost D.degree] at hzero
      exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
        D.stage.F D.stage.selected Gamma pchar D.degree
        D.stage.characteristic_bound D.stage.degree_le D.stage.solution
        D.stage.regular D.stage.on_prime
        (x i) (D.stage.u0 i) (D.stage.u1 i)
        (D.degree * degreeCost + unitCost) hzero
    have hrawTerminal := incidence_after_exempt_nodes
      (fun gamma i ↦ D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a - k)
        (D.degree * degreeCost + unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw : Gamma.card * (a - k) ≤
        (S.nodes.card - k) * ((d - k) * degreeCost + unitCost) := by
      simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
        hrawTerminal
    have hmain : Gamma.card * (a - d) ≤ U * degreeCost + V * unitCost :=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail := hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)

end

end ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
