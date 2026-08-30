import ProximityPrize.SubmissionLower.GW
namespace ProximityPrize.SubmissionLower.ContactTwoTailRectangleStageBounds6734Research
open ContactFlagBezout6543Research ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research ContactMovingOuterBudget6719Research
open ContactReducedTaylorProfileResearch ContactTwoTailParameters6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
open ContactTwoTailFixedStageBound6734Research
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def fixedProfiles : List (ℕ × ℕ × ℕ) := [
  (1225,42,9), (1224,43,9), (1226,40,10), (1226,42,9),
  (1225,43,9), (1227,40,10), (1224,44,8), (1223,45,8),
  (1223,44,9), (1225,44,8), (1224,45,8), (1224,44,9),
  (1235,33,9), (1235,32,10), (1234,34,9), (1234,33,10),
  (1236,33,9), (1236,32,10), (1235,34,9), (1235,33,10)]

theorem fixedStageBound_of_profiles (a b s : ℕ)
    (h : (a,b,s) ∈ fixedProfiles) : FixedStageBound a b s := by
  simp only [fixedProfiles, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    apply fixedStageBound_of_numeric <;> intros <;>
    norm_num [ContactMovingAgreementCertificate6719Research.support,
      ContactProperDelayedTailCertificate6732Research.fixedSupport,
      ContactTwoTailParameters6734Research.n,
      ContactTwoTailParameters6734Research.w,
      ContactTwoTailParameters6734Research.errors,
      ContactTwoTailParameters6734Research.agreements,
      ContactTwoTailParameters6734Research.gap,
      ContactTwoTailParameters6734Research.prime,
      ContactTwoTailFixedSelectedGeneric6734Research.firstTail,
      ContactTwoTailFixedSelectedGeneric6734Research.secondTail,
      ContactTwoTailFixedSelectedGeneric6734Research.fixedFlag,
      ContactReducedTaylorProfileResearch.reducedResidualAgreementFlag,
      ContactReducedTaylorProfileResearch.reducedAgreementDirection,
      ContactIdentityCurveProvider6731Research.identityCurveDegree,
      ContactMovingOuterBudget6719Research.paddedCut,
      ContactMovingPositiveLedger6719Research.centreFlag,
      ContactMovingPositiveLedger6719Research.directionFlag,
      ContactFlagBezout6543Research.flagMixed,
      ContactFlagBezout6543Research.unitZFlag,
      ContactFlagBezout6543Research.unitYZFlag,
      ContactFlagBezout6543Research.add_zOnly,
      ContactFlagBezout6543Research.add_yz,
      ContactFlagBezout6543Research.add_all,
      ContactFlagBezout6543Research.nsmul_zOnly,
      ContactFlagBezout6543Research.nsmul_yz,
      ContactFlagBezout6543Research.nsmul_all] at * <;> omega
end ProximityPrize.SubmissionLower.ContactTwoTailRectangleStageBounds6734Research
