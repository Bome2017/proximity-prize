import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
import ProximityPrize.SubmissionLower.ContactReducedTaylorYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

/-!
# Unconditional fixed selected cell at agreement 182414

This module instantiates the generic sharp-Taylor active-YZ factor provider
and the profile-generic tight selected-family combiner at the fixed meet used
by the score-66.70 arithmetic.
-/

namespace ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research

open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint
open ContactFactorCaps ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactTaylorNumerators
open ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research
open ContactRegularFactorFlag6600Research
open ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch
open ContactResidualSupportParametersResearch.ResidualSupportParameters
open ContactFlagBezout6543Research
open ContactRobustFixedMeet6656Research
open ContactSharpTaylorFixedMeet6656Research
open ContactSharpTaylorYZFactorProviderResearch
open ContactReducedTaylorYZFactorProviderResearch
open ContactProfileYZFactorLedgerResearch
open ContactProfileFixedSelectedCombinerResearch
open ContactFixedMeetProfile6670Research
open ContactNestedWeightedFlagResearch ContactSingularDegreeBounds
open ContactImplicitContactLift

noncomputable section

set_option maxHeartbeats 7000000
set_option maxRecDepth 100000

variable {K Iota : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

/-- The target interpolation box supplies the preserved `(8,43,933)` support
needed by the residual recursion. -/
theorem fixedSupport_of_mem_box
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap) :
    ResidualSupportData fixedSupport F := by
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights F 9).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 970 ∧ d 2 ≤ 9 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5836032 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 9
    norm_num
    exact hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights F 44).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 970 ∧ d 2 ≤ 9 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5836032 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 44
    norm_num
    norm_num at hb
    omega
  · apply (weightedTotalDegree_le_iff residualTotalWeights F 979).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 970 ∧ d 2 ≤ 9 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5836032 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 979
    norm_num
    norm_num at hb
    omega

/-- Canonical fixed-profile residual stage for one geometric factor of one
actual positive-`R` factor. -/
def fixedRegularGeometricResidualStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x prime fixedProfile.errors (geometricFlag K g) fixedProfile.w
      fixedSupport := by
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt
        (by norm_num [fixedProfile, prime])
  have hsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_mem_box R.1 hRdata.2.2
  exact regularGeometricResidualStageOfSupport fixedSupport Q selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
    hsupport (by norm_num [fixedProfile, prime]) g

/-- Geometric sharp-YZ bounds aggregate to the same direction-generic ledger
on one actual positive-`R` factor. -/
theorem regular_factor_seed_bound_of_geometric_sharp_yz_counts
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (R : RegularIndex Q)
    (hcount : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected
          (regularSeeds Q selected Gamma R) g).card * fixedProfile.gap ^ 2 ≤
        factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
          (geometricFlag K g)) :
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (surfaceNestedFlag R.1) := by
  obtain ⟨hRirred, _, _⟩ := directFactor_data Q R.1 hQ
    fixedProfile.weightedCap fixedProfile.w fixedProfile.seedTotalCap
      fixedProfile.slopeCap hbox R.2
  have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1 = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRirred.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hcaps := geometricFlag_nested_budgets K R.1 hRirred.ne_zero
  calc
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
        (∑ g : GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card) *
          fixedProfile.gap ^ 2 := Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected
          (regularSeeds Q selected Gamma R) g).card * fixedProfile.gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K R.1,
        factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
          (geometricFlag K g) := Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (surfaceNestedFlag R.1) :=
      sum_factorRegularLedgerYZForDirection_le_nested fixedProfile
        fixedSharpDirection (geometricFlag K) (surfaceNestedFlag R.1)
        fixed_ledger_unit_monotone.1 fixed_ledger_unit_monotone.2
        (by simpa only [surfaceNestedFlag_all] using hcaps.1)
        (by simpa only [surfaceNestedFlag_ys] using hcaps.2.1)
        (by simpa only [surfaceNestedFlag_total] using hcaps.2.2)

/-- Every actual positive-`R` factor receives its sharp-YZ ledger from the
canonical active-YZ terminal families. -/
theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (surfaceNestedFlag R.1) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  apply regular_factor_seed_bound_of_geometric_sharp_yz_counts Q hQ hbox
    selected Gamma R
  intro g
  let S := fixedRegularGeometricResidualStage Q hQ hbox selected Gamma
    nodes x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds Q selected Gamma R) g).trans
      (regularSeeds_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = fixedProfile.n := by
    simpa [S, fixedRegularGeometricResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g,
      fixedProfile.agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
      fixedRegularGeometricResidualStage,
      regularGeometricResidualStageOfSupport,
      geometricResidualStageOfSupport] using
        hagreement gamma (hgeomSub hgamma)
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRne : R.1 ≠ 0 := hRdata.1.ne_zero
  have hglobal := regularFlag_budgets fixedProfile Q hQ
    (by norm_num [fixedProfile]) hbox
  have hRZ : (regularFlag Q R).zOnly ≤ fixedProfile.seedTotalCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.1
  have hRY : (regularFlag Q R).yz ≤ fixedProfile.yCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.1
  have hRS : (regularFlag Q R).all ≤ fixedProfile.slopeCap :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ R)).trans hglobal.2.2
  have hgZ : (geometricFlag K g).zOnly ≤ R.1.degreeOf (3 : Fin 4) :=
    (curveNestedFlag_z_le_degree g.1).trans
      (geometricFactor_degree_le K R.1 hRne g 2)
  have hgY : (geometricFlag K g).yz ≤ R.1.degreeOf (1 : Fin 4) :=
    (curveNestedFlag_yz_le_degree g.1).trans
      (geometricFactor_degree_le K R.1 hRne g 0)
  have hgS : (geometricFlag K g).all ≤ R.1.degreeOf (2 : Fin 4) := by
    rw [geometricFlag, curveNestedFlag_all_eq_degree]
    exact geometricFactor_degree_le K R.1 hRne g 1
  have hflagY : (geometricFlag K g).yz + (geometricFlag K g).all ≤ 53 := by
    calc
      _ ≤ fixedProfile.yCap + fixedProfile.slopeCap :=
        Nat.add_le_add (hgY.trans hRY) (hgS.trans hRS)
      _ = 53 := by norm_num [fixedProfile, Profile.yCap]
  have hflagS : (geometricFlag K g).all ≤ 9 := by
    exact (hgS.trans hRS).trans_eq (by norm_num [fixedProfile])
  have hflagZ : (geometricFlag K g).zOnly + (geometricFlag K g).yz +
      (geometricFlag K g).all ≤ 1023 := by
    calc
      _ ≤ fixedProfile.seedTotalCap + fixedProfile.yCap +
          fixedProfile.slopeCap :=
        Nat.add_le_add
          (Nat.add_le_add (hgZ.trans hRZ) (hgY.trans hRY))
          (hgS.trans hRS)
      _ = 1023 := by norm_num [fixedProfile, Profile.yCap]
  have hprojection : TerminalAdaptiveProjectionFamiliesReducedYZ fixedSupport S :=
    terminalAdaptiveProjectionFamiliesReducedYZ_of_active_yz_caps
      fixedSupport S 53 9 1023 11272107 2097136
      hflagY hflagS hflagZ
      (by norm_num [fixedProfile, fixedSupport])
      (by norm_num [fixedProfile, fixedSupport])
      ⟨by norm_num [prime], by norm_num [prime], by norm_num [prime]⟩
      (by norm_num [prime])
  exact recursive_scaled_factorReducedYZ_of_adaptive_projection_families
    (polynomialEmbedding_injective K) fixedProfile fixedSupport
    S hnodesS hagreementS
    fixed_characteristic_gates.2.2.2.2.1
    fixed_characteristic_gates.2.2.2.2.2.1
    fixed_degree_part_bound fixed_unit_part_bound hprojection

theorem regularFactor_sum_surfaceWt_le
    (weights : Fin 4 → ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    (∑ R : RegularIndex Q,
      MvPolynomial.weightedTotalDegree weights R.1) ≤
      MvPolynomial.weightedTotalDegree weights Q := by
  classical
  have hb := sum_weighted_degrees_le_of_prod_dvd weights
    (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ)
  simp only [id_eq] at hb
  rw [← Finset.sum_attach (positiveRFactors Q)
    (fun R ↦ MvPolynomial.weightedTotalDegree weights R)] at hb
  simpa only [Finset.attach_eq_univ] using hb

theorem regularNestedFlag_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    (∑ R : RegularIndex Q, (surfaceNestedFlag R.1).all) ≤
        MvPolynomial.weightedTotalDegree residualSWeights Q ∧
      (∑ R : RegularIndex Q,
        ((surfaceNestedFlag R.1).yz + (surfaceNestedFlag R.1).all)) ≤
        MvPolynomial.weightedTotalDegree residualYSWeights Q ∧
      (∑ R : RegularIndex Q,
        ((surfaceNestedFlag R.1).zOnly + (surfaceNestedFlag R.1).yz +
          (surfaceNestedFlag R.1).all)) ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights Q := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [surfaceNestedFlag_all] using
      regularFactor_sum_surfaceWt_le residualSWeights Q hQ
  · simpa only [surfaceNestedFlag_ys] using
      regularFactor_sum_surfaceWt_le residualYSWeights Q hQ
  · simpa only [surfaceNestedFlag_total] using
      regularFactor_sum_surfaceWt_le residualTotalWeights Q hQ

theorem sum_fixedNestedLedger_of_pointwise
    {Q : MvPolynomial (Fin 4) K} (count : RegularIndex Q → ℕ)
    (hcount : ∀ F : RegularIndex Q, count F * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (surfaceNestedFlag F.1)) :
    (∑ F : RegularIndex Q, count F * fixedProfile.gap ^ 2) ≤
      ∑ F : RegularIndex Q, factorRegularLedgerYZForDirection fixedProfile
        fixedSharpDirection (surfaceNestedFlag F.1) := by
  exact Finset.sum_le_sum (fun F _ ↦ hcount F)

/-- Direction-generic nested-weight aggregation for the target regular ledger. -/
theorem sum_regular_factor_counts_le_numerator
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (count : RegularIndex Q → ℕ)
    (hcount : ∀ F : RegularIndex Q, count F * fixedProfile.gap ^ 2 ≤
      factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        (surfaceNestedFlag F.1)) :
    (∑ F : RegularIndex Q, count F) * fixedProfile.gap ^ 2 ≤
      fixedSharpYZRegularNumerator := by
  calc
    (∑ F : RegularIndex Q, count F) * fixedProfile.gap ^ 2 =
        ∑ F : RegularIndex Q, count F * fixedProfile.gap ^ 2 := by
      rw [Finset.sum_mul]
    _ ≤ ∑ F : RegularIndex Q,
        factorRegularLedgerYZForDirection fixedProfile
        fixedSharpDirection (surfaceNestedFlag F.1) :=
      sum_fixedNestedLedger_of_pointwise count hcount
    _ ≤ factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection
        fixedNestedSurfaceFlag := by
      have hnested := regularNestedFlag_budgets Q hQ
      have hsupport := fixedSupport_of_mem_box Q hbox
      exact sum_factorRegularLedgerYZForDirection_le_nested fixedProfile
        fixedSharpDirection
        (fun F : RegularIndex Q ↦ surfaceNestedFlag F.1)
        fixedNestedSurfaceFlag fixed_ledger_unit_monotone.1
        fixed_ledger_unit_monotone.2
        (hnested.1.trans hsupport.s_weight)
        (hnested.2.1.trans hsupport.ys_weight)
        (hnested.2.2.trans hsupport.total_weight)
    _ = fixedSharpYZRegularNumerator := rfl

/-- Strong inclusive fixed-cell cap.  This is two below the sum of the two
strict per-branch ceilings recorded in the arithmetic module. -/
theorem fixed_selected_count_le_exact_cap
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors) :
    Gamma.card ≤ 265927711059427574 := by
  have hA : FixedParameterAlignment fixedProfile fixedTightProfile :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h := global_count_le_regular_div_add_tight_countCap
    fixedProfile fixedTightProfile hA Q hQ hbox
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile, prime, Profile.algebraicCap])
    (by norm_num [fixedTightProfile, prime,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa])
    (by norm_num [fixedTightProfile, prime,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
      ContactTightSingularLedgerResearch.TightParameters.kappa])
    (by norm_num [fixedProfile])
    (by norm_num [fixedProfile])
    selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement
    hnoPencil
    (fun F ↦ surfaceNestedFlag F.1)
    (factorRegularLedgerYZForDirection fixedProfile fixedSharpDirection)
    (fun count _hcount ↦
      sum_regular_factor_counts_le_numerator Q hQ hbox count _hcount)
    (regular_factor_seed_bound Q hQ hbox selected Gamma nodes x u0 u1
      hinj hnodes hdegree hagreement hnoPencil)
  rw [fixed_sharp_yz_regular_numerator_exact,
    fixed_tight_singular_count_cap_exact] at h
  norm_num [fixedProfile, Profile.gap] at h ⊢
  exact h

/-- Safe fixed cost used by the six-ledger arithmetic: the sum of the two
strict branch ceilings. -/
theorem fixed_selected_count_le_fixedCountCeiling
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      fixedProfile.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma fixedProfile.w
      fixedProfile.errors) :
    Gamma.card ≤ fixedCountCeiling := by
  have h := fixed_selected_count_le_exact_cap Q hQ hbox selected Gamma
    nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  rw [fixed_count_ceiling_exact]
  exact h.trans (by norm_num)

end

end ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research
