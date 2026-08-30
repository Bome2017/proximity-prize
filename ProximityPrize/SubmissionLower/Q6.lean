import ProximityPrize.SubmissionLower.P6
import ProximityPrize.SubmissionLower.Q5
import ProximityPrize.SubmissionLower.RFreeDerivativeCertificate
namespace ProximityPrize.SubmissionLower.ContactTwoTailSelectedBound6734Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactIdentityResidualGlobalFlagResearch ContactResidualSupportParametersResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactKernelCommonGCDResearch ContactKernelSelectedInterpolation6733Research
open ContactTwoTailParameters6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
open ContactTwoTailRectangleStageBounds6734Research
open ContactTwoTailResidualGeneric6734Research
open ContactTwoTailResidualRectangles6734Research
open ContactGCDCumulativeFlagsResearch ContactImplicitContactLift
open ContactRegularFactorGate RFreeDerivativeTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
local instance : CharP K prime := by
 simpa [prime, ContactParameters6600Research.prime] using
   ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem selected_recursive_cover
   (U : Fin 2 → I → K) (seeds : Finset K)
   (A : K → Finset I) (selected : K → Polynomial K)
   (S : SelectedInterpolants (U 0) (U 1))
   (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
   (hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card)
   (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
     (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i) :
   ∀ gamma ∈ seeds,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC := by
 intro gamma hgamma
 have hv := S.universal_vanishing gamma (selected gamma) (A gamma)
   (hdegree gamma hgamma) (by
     have hh := hcard gamma hgamma
     norm_num [I, IRSProfile.Index, errors, n, agreements,
       ContactKernelSelectedInterpolation6733Research.agreements6733] at hh ⊢
     exact hh) (hvalues gamma hgamma)
 apply recursive_branch_of_three_vanishings
 exact hv.1
 exact hv.2.1
 exact hv.2.2
theorem selected_full_domain_agreement
   (U : Fin 2 → I → K) (seeds : Finset K)
   (A : K → Finset I) (selected : K → Polynomial K)
   (hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card)
   (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
     (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i) :
   ∀ gamma ∈ seeds, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) =
         U 0 i + gamma * U 1 i)).card := by
 intro gamma hgamma
 have hsub : A gamma ⊆
     (Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) =
         U 0 i + gamma * U 1 i) := by
   intro i hi
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalues gamma hgamma i hi⟩
 have hsize := (hcard gamma hgamma).trans (Finset.card_le_card hsub)
 norm_num [I, IRSProfile.Index, errors, n, agreements] at hsize ⊢
 exact hsize
theorem selected_card_le_of_rectangle
   (fixedCost lt ly ls us : ℕ)
   (validFirst : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (validSecond : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (hbudget : fixedCost + residualCost lt ly ls us < mcaBudget)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hfixed : (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤ fixedCost)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (hsUpper : wt residualSWeights S.G ≤ us)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G) :
   Gamma.card ≤ mcaBudget := by
 have hGeq : gcd123 S.QA S.QB S.QC = S.G := by
   simpa [gcd123, gcd12, S.H_eq] using S.G_eq.symm
 have hHcaps := (mem_flagGlobalCoefficientBox_iff S.H
   profileA.weightedCap w profileA.totalCap profileA.slopeCap
   (by norm_num [profileA, Profile.weightedCap, agreements, errors, n])).mp S.H_flagA
 have hHbox : S.H ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileA.weightedCap w 1281 profileA.slopeCap := by
   apply (mem_flagGlobalCoefficientBox_iff S.H profileA.weightedCap w 1281
     profileA.slopeCap
     (by norm_num [profileA, Profile.weightedCap, agreements, errors, n])).mpr
   exact ⟨S.H_total_le, hHcaps.2.1, hHcaps.2.2⟩
 have hfirst := firstResidualCell_count_lt lt ly ls us validFirst
   S.QA S.QB S.QC S.QA_ne S.QB_ne S.QA_flag S.QB_flag
   (by simpa only [hGeq] using htotalLower)
   (by simpa only [hGeq] using hysLower)
   (by simpa only [hGeq] using hsLower)
   (by simpa only [hGeq] using hsUpper)
   selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
 have hsecond := secondResidualCell_count_lt lt ly ls us validSecond
   S.QA S.QB S.QC S.QA_ne S.QC_ne S.QC_flag (by
     have hh : gcd S.QA S.QB ∈
         ContactFlagInterpolation6641Research.globalCoefficientBox K
           profileA.weightedCap w 1281 profileA.slopeCap := by
       rw [← S.H_eq]
       exact hHbox
     simpa only [gcd12] using hh)
   (by simpa only [hGeq] using htotalLower)
   (by simpa only [hGeq] using hysLower)
   (by simpa only [hGeq] using hsLower)
   (by simpa only [hGeq] using hsUpper)
   selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
 have hpartition : Gamma.card =
     (firstResidualSeeds selected Gamma S.QA S.QB).card +
     (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card +
     (fixedSeeds selected Gamma S.QA S.QB S.QC).card :=
   (partition_card selected Gamma S.QA S.QB S.QC).symm
 unfold residualCost at hbudget
 omega
theorem selected_card_le_of_ordinary_rectangle
   (a b s lt ly ls us : ℕ)
   (stageBound : FixedStageBound a b s)
   (validFirst : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (validSecond : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (hbudget : rectangleCost a b s lt ly ls us < mcaBudget)
   (hsSmall : s + 2 < prime)
   (hseedSmall : (2 * (s + 2) - 1) * (a + b + s + 3) < prime)
   (himplicitYSmall : (fixedTightProfile a b s).implicitYCap < prime)
   (hmixedSmall : 2 * (fixedTightProfile a b s).implicitYCap *
     (fixedTightProfile a b s).algebraicCap < prime)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ a + b + s + 3)
   (hysUpper : wt residualYSWeights S.G ≤ b + s + 3)
   (hsUpper : wt residualSWeights S.G ≤ s + 2)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G)
   (hus : us = s + 2) :
   Gamma.card ≤ mcaBudget := by
 have hGeq : gcd123 S.QA S.QB S.QC = S.G := by
   simpa [gcd123, gcd12, S.H_eq] using S.G_eq.symm
 have hGcapsC := (mem_flagGlobalCoefficientBox_iff S.G
   profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (by norm_num [profileC, Profile.weightedCap, agreements, errors, n])).mp S.G_flagC
 have hGflag : S.G ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     (42 * agreements) w (a + b + s + 3) (s + 2) := by
   apply (mem_flagGlobalCoefficientBox_iff S.G (42 * agreements) w
     (a + b + s + 3) (s + 2) (by norm_num [agreements, errors, n])).mpr
   refine ⟨htotalUpper, hsUpper, ?_⟩
   simpa [profileC, Profile.weightedCap] using hGcapsC.2.2
 have hGbox : S.G ∈ globalCoefficientBox K
     (42 * agreements) w (a + b + s + 3) (s + 2) :=
   ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
     (K := K) (D := 42 * agreements) (w := w)
     (L := a + b + s + 3) (s := s + 2) S.G hGflag
 have hsupport : ResidualSupportData
     (ContactMovingAgreementCertificate6719Research.support a b s) S.G := by
   refine ⟨?_, ?_, ?_⟩
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hsUpper
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hysUpper
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using htotalUpper
 let fixedDelta := fixedSeeds selected Gamma S.QA S.QB S.QC
 have hfixedSub : fixedDelta ⊆ Gamma := by
   simpa only [fixedDelta] using fixedSeeds_subset selected Gamma S.QA S.QB S.QC
 have hfixedSolution : ∀ gamma ∈ fixedDelta,
     specialization K (selected gamma) gamma S.G = 0 := by
   intro gamma hgamma
   have hv := fixedSeeds_vanish selected Gamma S.QA S.QB S.QC gamma hgamma
   simpa only [hGeq] using hv
 have hfixed := fixed_count_le a b s hsSmall stageBound hseedSmall
   himplicitYSmall hmixedSmall S.G S.G_ne hGbox hsupport selected fixedDelta u0 u1
   hfixedSolution
   (fun gamma hgamma => hdegree gamma (hfixedSub hgamma))
   (fun gamma hgamma => hagreement gamma (hfixedSub hgamma))
   (noLargeSelectedPencil_mono selected Gamma fixedDelta w errors hfixedSub hnoPencil)
 apply selected_card_le_of_rectangle
   (fixedRegularCost a b s + (fixedTightProfile a b s).countCap)
   lt ly ls us validFirst validSecond
   (by simpa only [rectangleCost] using hbudget) S selected Gamma
   (by simpa only [fixedDelta] using hfixed) hcover hdegree hagreement hnoPencil
   (by simpa only [hus] using hsUpper) htotalLower hysLower hsLower

def RectangleSideConditions (a b s : ℕ) : Prop :=
 s + 2 < prime ∧
 (2 * (s + 2) - 1) * (a + b + s + 3) < prime ∧
 (fixedTightProfile a b s).implicitYCap < prime ∧
 2 * (fixedTightProfile a b s).implicitYCap *
   (fixedTightProfile a b s).algebraicCap < prime
theorem rectangleSideConditions_of_profiles (a b s : ℕ)
   (h : (a,b,s) ∈ fixedProfiles) :
   RectangleSideConditions a b s := by
 simp only [fixedProfiles, List.mem_cons, List.not_mem_nil, or_false,
   Prod.mk.injEq] at h
 rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
   norm_num [RectangleSideConditions,
     ContactTwoTailParameters6734Research.prime,
     ContactTwoTailParameters6734Research.n,
     ContactTwoTailParameters6734Research.w,
     ContactTwoTailParameters6734Research.errors,
     ContactTwoTailParameters6734Research.agreements,
     ContactTwoTailFixedSelectedGeneric6734Research.fixedTightProfile,
     ContactTightSingularLedgerResearch.TightParameters.errors,
     ContactTightSingularLedgerResearch.TightParameters.gap,
     ContactTightSingularLedgerResearch.TightParameters.kappa,
     ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
     ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
     ContactTightSingularLedgerResearch.TightParameters.agreement,
     ContactTightSingularLedgerResearch.TightParameters.aggregateCost,
     ContactTightSingularLedgerResearch.TightParameters.coreNumerator,
     ContactTightSingularLedgerResearch.TightParameters.tightNumerator,
     ContactTightSingularLedgerResearch.TightParameters.countCap]

theorem selected_card_le_of_derivative_rectangle
   (lt : ℕ) (hlt : lt = 0 ∨ lt = 1279)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ 1280)
   (hysUpper : wt residualYSWeights S.G ≤ 55)
   (hslopeEq : wt residualSWeights S.G = 12)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : 54 ≤ wt residualYSWeights S.G) :
   Gamma.card ≤ mcaBudget := by
 let J := MvPolynomial.pderiv (2 : Fin 4) S.G
 have hdegreeR : S.G.degreeOf 2 = 12 := by
   rw [← originalCumulativeFlag_all]
   exact hslopeEq
 have hJne : J ≠ 0 := by
   apply R_derivative_nonzero S.G prime
   · rw [hdegreeR]
     norm_num
   · rw [hdegreeR]
     norm_num [prime]
 have hGcaps := (mem_flagGlobalCoefficientBox_iff S.G
   profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (by norm_num [profileC, Profile.weightedCap, agreements, n, errors])).mp
     S.G_flagC
 have hJcontact : wt (contactWeights w) J ≤ 7514273 := by
   have hh := pderiv_weight_sub_bound (contactWeights w) S.G (2 : Fin 4)
     (profileC.weightedCap - 1) hGcaps.2.2
   change wt (contactWeights w) J ≤
     (profileC.weightedCap - 1) - (w - 1) at hh
   norm_num [profileC, Profile.weightedCap, agreements, n, errors, w] at hh ⊢
   exact hh
 have hJtotal : wt residualTotalWeights J ≤ 1279 := by
   have hh := pderiv_weight_sub_bound residualTotalWeights S.G (2 : Fin 4)
     1280 htotalUpper
   change wt residualTotalWeights J ≤ 1280 - 1 at hh
   omega
 have hJys : wt residualYSWeights J ≤ 54 := by
   have hh := pderiv_weight_sub_bound residualYSWeights S.G (2 : Fin 4)
     55 hysUpper
   change wt residualYSWeights J ≤ 55 - 1 at hh
   omega
 have hJslope : wt residualSWeights J ≤ 11 := by
   have hh := pderiv_weight_sub_bound residualSWeights S.G (2 : Fin 4)
     (wt residualSWeights S.G) le_rfl
   change wt residualSWeights J ≤ wt residualSWeights S.G - 1 at hh
   omega
 have hJflagTight : J ∈
     ContactFlagInterpolation6641Research.globalCoefficientBox K
       7514274 w 1279 11 := by
   apply (mem_flagGlobalCoefficientBox_iff J 7514274 w 1279 11
     (by norm_num)).mpr
   exact ⟨hJtotal, hJslope, hJcontact⟩
 have hJcaps := (mem_flagGlobalCoefficientBox_iff J 7514274 w 1279 11
   (by norm_num)).mp hJflagTight
 have hJflag : J ∈
     ContactFlagInterpolation6641Research.globalCoefficientBox K
       (42 * agreements) w 1279 11 := by
   apply (mem_flagGlobalCoefficientBox_iff J (42 * agreements) w 1279 11
     (by norm_num [agreements, n, errors])).mpr
   refine ⟨hJcaps.1, hJcaps.2.1, ?_⟩
   exact hJcaps.2.2.trans (by norm_num [agreements, n, errors])
 have hJbox : J ∈ globalCoefficientBox K (42 * agreements) w 1279 11 :=
   ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
     (K := K) (D := 42 * agreements) (w := w) (L := 1279) (s := 11)
       J hJflag
 have hJsupport : ResidualSupportData
     (ContactMovingAgreementCertificate6719Research.support 1225 42 9) J := by
   refine ⟨?_, ?_, ?_⟩
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hJslope
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hJys
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hJtotal
 let fixedDelta := fixedSeeds selected Gamma S.QA S.QB S.QC
 have hfixedSub : fixedDelta ⊆ Gamma := by
   simpa only [fixedDelta] using fixedSeeds_subset selected Gamma S.QA S.QB S.QC
 have hfixedSolution : ∀ gamma ∈ fixedDelta,
     specialization K (selected gamma) gamma J = 0 := by
   intro gamma hgamma
   obtain ⟨points, hpoints, hpointscard⟩ :=
     Finset.exists_subset_card_eq (hagreement gamma (hfixedSub hgamma))
   have hvalues : ∀ i ∈ points,
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i := by
     intro i hi
     exact (Finset.mem_filter.mp (hpoints hi)).2
   have hz := RFreeDerivativeCertificate.derivative_specialization_zero
     u0 u1 S (selected gamma) gamma points
       (by simpa [agreements, n, errors] using hpointscard)
       (by simpa [w] using hdegree gamma (hfixedSub hgamma)) hvalues
       hysLower (by omega) (by omega)
   simpa only [J, RFreeDerivativeTransport.globalSpecialization,
     ContactTranslation.specialization] using hz
 have hside := rectangleSideConditions_of_profiles 1225 42 9 (by
   simp [fixedProfiles])
 have hfixed := fixed_count_le 1225 42 9 hside.1
   (fixedStageBound_of_profiles 1225 42 9 (by simp [fixedProfiles]))
   hside.2.1 hside.2.2.1 hside.2.2.2 J hJne hJbox hJsupport
   selected fixedDelta u0 u1 hfixedSolution
   (fun gamma hgamma => hdegree gamma (hfixedSub hgamma))
   (fun gamma hgamma => hagreement gamma (hfixedSub hgamma))
   (noLargeSelectedPencil_mono selected Gamma fixedDelta w errors
     hfixedSub hnoPencil)
 have hbudget := derivativeRectangleCost_lt lt hlt
 have hvalid : (lt,53,11,12) ∈ residualProfiles := by
   rcases hlt with rfl | rfl <;> simp [residualProfiles]
 have hvalidities := residualValidities_of_profiles lt 53 11 12 hvalid
 apply selected_card_le_of_rectangle derivativeFixedCost lt 53 11 12
   hvalidities.1 hvalidities.2
   (by simpa only [derivativeRectangleCost] using hbudget)
   S selected Gamma (by simpa only [fixedDelta, derivativeFixedCost] using hfixed)
   hcover hdegree hagreement hnoPencil (by omega) htotalLower (by omega) (by omega)
theorem selected_card_le_of_certified_rectangle
   (a b s lt ly ls us : ℕ)
   (stageBound : FixedStageBound a b s)
   (validFirst : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (validSecond : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (hbudget : rectangleCost a b s lt ly ls us < mcaBudget)
   (hside : RectangleSideConditions a b s)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ a + b + s + 3)
   (hysUpper : wt residualYSWeights S.G ≤ b + s + 3)
   (hsUpper : wt residualSWeights S.G ≤ s + 2)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G)
   (hus : us = s + 2) :
   Gamma.card ≤ mcaBudget :=
 selected_card_le_of_ordinary_rectangle a b s lt ly ls us stageBound validFirst validSecond
   hbudget hside.1 hside.2.1 hside.2.2.1 hside.2.2.2 S selected Gamma hcover
   hdegree hagreement hnoPencil htotalUpper hysUpper hsUpper htotalLower hysLower
   hsLower hus

theorem ordinaryProfile_components (a b s lt ly ls us : ℕ)
   (h : (a,b,s,lt,ly,ls,us) ∈ ordinaryProfiles) :
   (a,b,s) ∈ fixedProfiles ∧ (lt,ly,ls,us) ∈ residualProfiles := by
 simp only [ordinaryProfiles, List.mem_cons, List.not_mem_nil, or_false,
   Prod.mk.injEq] at h
 rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
   simp [fixedProfiles, residualProfiles]

theorem selected_card_le_of_listed_rectangle
   (a b s lt ly ls us : ℕ)
   (hprofile : (a,b,s,lt,ly,ls,us) ∈ ordinaryProfiles)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ a + b + s + 3)
   (hysUpper : wt residualYSWeights S.G ≤ b + s + 3)
   (hsUpper : wt residualSWeights S.G ≤ s + 2)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G)
   (hus : us = s + 2) :
   Gamma.card ≤ mcaBudget := by
 have hcomponents := ordinaryProfile_components a b s lt ly ls us hprofile
 have hvalid := residualValidities_of_profiles lt ly ls us hcomponents.2
 exact selected_card_le_of_certified_rectangle a b s lt ly ls us
   (fixedStageBound_of_profiles a b s hcomponents.1) hvalid.1 hvalid.2
   (rectangleCost_lt_of_profiles a b s lt ly ls us hprofile)
   (rectangleSideConditions_of_profiles a b s hcomponents.1)
   S selected Gamma hcover hdegree hagreement hnoPencil htotalUpper hysUpper
   hsUpper htotalLower hysLower hsLower hus
theorem selectedNoLargePencilBound6734 :
   SelectedNoLargePencilBound IRSProfile.domain 131071 errors mcaBudget := by
 intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
 have hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w := by
   simpa [w] using hdegreeRaw
 have hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card := by
   simpa [errors] using hcardRaw
 have hagreement := selected_full_domain_agreement U seeds A selected hcard hvalues
 have hno : NoLargeSelectedPencil selected seeds w errors := by
   intro P0 P1 hP0 hP1
   have hh := hnoRaw P0 P1 (by simpa [w] using hP0) (by simpa [w] using hP1)
   convert hh using 1
   · apply congrArg Finset.card
     ext gamma
     simp [pencilSeeds]
 let S : SelectedInterpolants (U 0) (U 1) :=
   Classical.choice (exists_selected_interpolants (U 0) (U 1))
 have hcover := selected_recursive_cover U seeds A selected S hdegree hcard hvalues
 have hGcapsC := (mem_flagGlobalCoefficientBox_iff S.G
   profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (by norm_num [profileC, Profile.weightedCap, agreements, errors, n])).mp S.G_flagC
 have hs12 : wt residualSWeights S.G ≤ 12 := by
   simpa [profileC] using hGcapsC.2.1
 have ht1281 : wt residualTotalWeights S.G ≤ 1281 := S.G_total_le
 have hy56 : wt residualYSWeights S.G ≤ 56 := S.G_ys_le
 rcases S.G_total_corner with ht1280 | hy46
 · rcases S.G_corner with hy55 | hs11
   · have htSplit : wt residualTotalWeights S.G = 1280 ∨
         wt residualTotalWeights S.G ≤ 1279 := by omega
     have hsSplit : wt residualSWeights S.G = 12 ∨
         wt residualSWeights S.G ≤ 11 := by omega
     rcases hsSplit with hsHigh | hsLow
     · have hySplit : 54 ≤ wt residualYSWeights S.G ∨
           wt residualYSWeights S.G ≤ 53 := by omega
       rcases hySplit with hyHigh | hyLow
       · rcases htSplit with htHigh | htLow
         · refine selected_card_le_of_derivative_rectangle 1279 (by simp)
             S selected seeds hcover hdegree hagreement hno ht1280 hy55 hsHigh
             ?_ hyHigh <;> omega
         · refine selected_card_le_of_derivative_rectangle 0 (by simp)
             S selected seeds hcover hdegree hagreement hno ht1280 hy55 hsHigh
             ?_ hyHigh <;> omega
       · rcases htSplit with htHigh | htLow
         · refine selected_card_le_of_listed_rectangle
             1227 40 10 1279 0 11 12 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1226 40 10 0 0 11 12 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
     · have hySplit : wt residualYSWeights S.G = 55 ∨
           wt residualYSWeights S.G ≤ 54 := by omega
       rcases htSplit with htHigh | htLow
       · rcases hySplit with hyHigh | hyLow
         · refine selected_card_le_of_listed_rectangle
             1225 43 9 1279 54 0 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1226 42 9 1279 0 0 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · rcases hySplit with hyHigh | hyLow
         · refine selected_card_le_of_listed_rectangle
             1224 43 9 0 54 0 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1225 42 9 0 0 0 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
   · have htSplit : wt residualTotalWeights S.G = 1280 ∨
         wt residualTotalWeights S.G ≤ 1279 := by omega
     have hySplit : wt residualYSWeights S.G = 56 ∨
         wt residualYSWeights S.G ≤ 55 := by omega
     have hsSplit : wt residualSWeights S.G = 11 ∨
         wt residualSWeights S.G ≤ 10 := by omega
     rcases htSplit with htHigh | htLow
     · rcases hySplit with hyHigh | hyLow
       · rcases hsSplit with hsHigh | hsLow
         · refine selected_card_le_of_listed_rectangle
             1224 44 9 1279 55 10 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1224 45 8 1279 55 0 10 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · rcases hsSplit with hsHigh | hsLow
         · refine selected_card_le_of_listed_rectangle
             1225 43 9 1279 0 10 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1225 44 8 1279 0 0 10 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
     · rcases hySplit with hyHigh | hyLow
       · rcases hsSplit with hsHigh | hsLow
         · refine selected_card_le_of_listed_rectangle
             1223 44 9 0 55 10 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1223 45 8 0 55 0 10 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · rcases hsSplit with hsHigh | hsLow
         · refine selected_card_le_of_listed_rectangle
             1224 43 9 0 0 10 11 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
         · refine selected_card_le_of_listed_rectangle
             1224 44 8 0 0 0 10 (by simp [ordinaryProfiles])
             S selected seeds hcover hdegree hagreement hno
             ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
 · have htSplit : wt residualTotalWeights S.G = 1281 ∨
       wt residualTotalWeights S.G ≤ 1280 := by omega
   have hySplit : wt residualYSWeights S.G = 46 ∨
       wt residualYSWeights S.G ≤ 45 := by omega
   have hsSplit : wt residualSWeights S.G = 12 ∨
       wt residualSWeights S.G ≤ 11 := by omega
   rcases htSplit with htHigh | htLow
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_listed_rectangle
           1235 33 10 1280 45 11 12 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · refine selected_card_le_of_listed_rectangle
           1235 34 9 1280 45 0 11 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_listed_rectangle
           1236 32 10 1280 0 11 12 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · refine selected_card_le_of_listed_rectangle
           1236 33 9 1280 0 0 11 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_listed_rectangle
           1234 33 10 0 45 11 12 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · refine selected_card_le_of_listed_rectangle
           1234 34 9 0 45 0 11 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_listed_rectangle
           1235 32 10 0 0 11 12 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
       · refine selected_card_le_of_listed_rectangle
           1235 33 9 0 0 0 11 (by simp [ordinaryProfiles])
           S selected seeds hcover hdegree hagreement hno
           ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> omega
end
end ProximityPrize.SubmissionLower.ContactTwoTailSelectedBound6734Research
