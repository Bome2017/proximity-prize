import ProximityPrize.SubmissionLower.Q4
import ProximityPrize.SubmissionLower.CI
namespace ProximityPrize.SubmissionLower.ContactTwoTailResidualRectangles6734Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
open ContactTwoTailParameters6734Research ContactTwoTailResidualGeneric6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def residualProfiles : List (ℕ × ℕ × ℕ × ℕ) := [
  (0,0,0,11), (0,54,0,11), (0,0,11,12),
  (1279,0,0,11), (1279,54,0,11), (1279,0,11,12),
  (0,0,0,10), (0,0,10,11), (0,55,0,10), (0,55,10,11),
  (1279,0,0,10), (1279,0,10,11), (1279,55,0,10), (1279,55,10,11),
  (0,45,0,11), (0,45,11,12),
  (1280,0,0,11), (1280,0,11,12), (1280,45,0,11), (1280,45,11,12),
  (0,53,11,12), (1279,53,11,12)]

theorem residualValidities_of_profiles (lt ly ls us : ℕ)
    (h : (lt,ly,ls,us) ∈ residualProfiles) :
    ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls) ∧
      ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls) := by
  simp only [residualProfiles, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    constructor <;> constructor <;>
    norm_num [firstStage, firstPivot, secondStage, secondPivot,
      ContactTwoTailParameters6734Research.n,
      ContactTwoTailParameters6734Research.w,
      ContactTwoTailParameters6734Research.errors,
      ContactTwoTailParameters6734Research.agreements,
      ContactTwoTailParameters6734Research.prime,
      ContactTwoTailParameters6734Research.Profile.weightedCap,
      ContactTwoTailParameters6734Research.profileA,
      ContactTwoTailParameters6734Research.profileB,
      ContactTwoTailParameters6734Research.profileC,
      UnequalParameters.errors, UnequalParameters.gap,
      UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
      UnequalParameters.agreement, UnequalParameters.mixedCost,
      UnequalParameters.regularNumerator, UnequalParameters.regularCountCap,
      TightParameters.errors, TightParameters.gap, TightParameters.kappa,
      TightParameters.algebraicCap, TightParameters.implicitYCap,
      TightParameters.agreement, TightParameters.aggregateCost,
      TightParameters.coreNumerator, TightParameters.tightNumerator,
      TightParameters.countCap, dot] at *

def ordinaryProfiles : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1225,42,9,0,0,0,11), (1224,43,9,0,54,0,11),
  (1226,40,10,0,0,11,12), (1226,42,9,1279,0,0,11),
  (1225,43,9,1279,54,0,11), (1227,40,10,1279,0,11,12),
  (1224,44,8,0,0,0,10), (1224,43,9,0,0,10,11),
  (1223,45,8,0,55,0,10), (1223,44,9,0,55,10,11),
  (1225,44,8,1279,0,0,10), (1225,43,9,1279,0,10,11),
  (1224,45,8,1279,55,0,10), (1224,44,9,1279,55,10,11),
  (1235,33,9,0,0,0,11), (1235,32,10,0,0,11,12),
  (1234,34,9,0,45,0,11), (1234,33,10,0,45,11,12),
  (1236,33,9,1280,0,0,11), (1236,32,10,1280,0,11,12),
  (1235,34,9,1280,45,0,11), (1235,33,10,1280,45,11,12)]

def residualCost (lt ly ls us : ℕ) : ℕ :=
  ((firstStage lt ly ls us).regularCountCap + (firstPivot lt ls).countCap + 1) +
  ((secondStage lt ly ls us).regularCountCap + (secondPivot lt ls).countCap + 1)

def rectangleCost (a b s lt ly ls us : ℕ) : ℕ :=
  fixedRegularCost a b s + (fixedTightProfile a b s).countCap +
    residualCost lt ly ls us

def derivativeFixedCost : ℕ :=
  fixedRegularCost 1225 42 9 + (fixedTightProfile 1225 42 9).countCap

def derivativeRectangleCost (lt ly ls us : ℕ) : ℕ :=
  derivativeFixedCost + residualCost lt ly ls us

theorem rectangleCost_lt_of_profiles (a b s lt ly ls us : ℕ)
    (h : (a,b,s,lt,ly,ls,us) ∈ ordinaryProfiles) :
    rectangleCost a b s lt ly ls us < mcaBudget := by
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
    norm_num [rectangleCost, residualCost, fixedRegularCost, fixedTightProfile,
      ContactTwoTailFixedSelectedGeneric6734Research.fixedProfile,
      ContactTwoTailFixedSelectedGeneric6734Research.fixedFlag,
      ContactTwoTailFixedSelectedGeneric6734Research.firstTail,
      ContactTwoTailFixedSelectedGeneric6734Research.secondTail,
      ContactMovingAgreementCertificate6719Research.support,
      ContactReducedTaylorProfileResearch.reducedResidualAgreementFlag,
      ContactReducedTaylorProfileResearch.reducedAgreementDirection,
      ContactMovingPositiveLedger6719Research.centreFlag,
      ContactMovingPositiveLedger6719Research.directionFlag,
      ContactMovingPositiveLedger6719Research.surfaceFlag,
      ContactFlagBezout6543Research.flagMixed,
      ContactFlagBezout6543Research.unitZFlag,
      ContactFlagBezout6543Research.unitYZFlag,
      ContactFlagBezout6543Research.add_zOnly,
      ContactFlagBezout6543Research.add_yz,
      ContactFlagBezout6543Research.add_all,
      ContactFlagBezout6543Research.nsmul_zOnly,
      ContactFlagBezout6543Research.nsmul_yz,
      ContactFlagBezout6543Research.nsmul_all,
      ContactTwoTailParameters6734Research.mcaBudget,
      ContactTwoTailParameters6734Research.capacity,
      ContactTwoTailParameters6734Research.listBudget,
      firstStage, firstPivot, secondStage, secondPivot,
      ContactTwoTailParameters6734Research.n,
      ContactTwoTailParameters6734Research.w,
      ContactTwoTailParameters6734Research.errors,
      ContactTwoTailParameters6734Research.agreements,
      ContactTwoTailParameters6734Research.prime,
      ContactTwoTailParameters6734Research.Profile.weightedCap,
      ContactTwoTailParameters6734Research.profileA,
      ContactTwoTailParameters6734Research.profileB,
      ContactTwoTailParameters6734Research.profileC,
      UnequalParameters.errors, UnequalParameters.gap,
      UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
      UnequalParameters.agreement, UnequalParameters.mixedCost,
      UnequalParameters.regularNumerator, UnequalParameters.regularCountCap,
      TightParameters.errors, TightParameters.gap, TightParameters.kappa,
      TightParameters.algebraicCap, TightParameters.implicitYCap,
      TightParameters.agreement, TightParameters.aggregateCost,
      TightParameters.coreNumerator, TightParameters.tightNumerator,
      TightParameters.countCap, dot]

theorem derivativeRectangleCost_lt (lt : ℕ)
    (h : lt = 0 ∨ lt = 1279) :
    derivativeRectangleCost lt 53 11 12 < mcaBudget := by
  rcases h with rfl | rfl <;>
    norm_num [derivativeRectangleCost, derivativeFixedCost, residualCost,
      fixedRegularCost, fixedTightProfile,
      ContactTwoTailFixedSelectedGeneric6734Research.fixedProfile,
      ContactTwoTailFixedSelectedGeneric6734Research.fixedFlag,
      ContactTwoTailFixedSelectedGeneric6734Research.firstTail,
      ContactTwoTailFixedSelectedGeneric6734Research.secondTail,
      ContactMovingAgreementCertificate6719Research.support,
      ContactReducedTaylorProfileResearch.reducedResidualAgreementFlag,
      ContactReducedTaylorProfileResearch.reducedAgreementDirection,
      ContactMovingPositiveLedger6719Research.centreFlag,
      ContactMovingPositiveLedger6719Research.directionFlag,
      ContactMovingPositiveLedger6719Research.surfaceFlag,
      ContactFlagBezout6543Research.flagMixed,
      ContactFlagBezout6543Research.unitZFlag,
      ContactFlagBezout6543Research.unitYZFlag,
      ContactFlagBezout6543Research.add_zOnly,
      ContactFlagBezout6543Research.add_yz,
      ContactFlagBezout6543Research.add_all,
      ContactFlagBezout6543Research.nsmul_zOnly,
      ContactFlagBezout6543Research.nsmul_yz,
      ContactFlagBezout6543Research.nsmul_all,
      ContactTwoTailParameters6734Research.mcaBudget,
      ContactTwoTailParameters6734Research.capacity,
      ContactTwoTailParameters6734Research.listBudget,
      firstStage, firstPivot, secondStage, secondPivot,
      ContactTwoTailParameters6734Research.n,
      ContactTwoTailParameters6734Research.w,
      ContactTwoTailParameters6734Research.errors,
      ContactTwoTailParameters6734Research.agreements,
      ContactTwoTailParameters6734Research.prime,
      ContactTwoTailParameters6734Research.Profile.weightedCap,
      ContactTwoTailParameters6734Research.profileA,
      ContactTwoTailParameters6734Research.profileB,
      ContactTwoTailParameters6734Research.profileC,
      UnequalParameters.errors, UnequalParameters.gap,
      UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
      UnequalParameters.agreement, UnequalParameters.mixedCost,
      UnequalParameters.regularNumerator, UnequalParameters.regularCountCap,
      TightParameters.errors, TightParameters.gap, TightParameters.kappa,
      TightParameters.algebraicCap, TightParameters.implicitYCap,
      TightParameters.agreement, TightParameters.aggregateCost,
      TightParameters.coreNumerator, TightParameters.tightNumerator,
      TightParameters.countCap, dot]
end ProximityPrize.SubmissionLower.ContactTwoTailResidualRectangles6734Research
