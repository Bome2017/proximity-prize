import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6731Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6731Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182071, 108, 24, 1205, 58, 11, 22328⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182071, 58, 11, 1205, 55, 12, 27619⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182071, 14201538, 1205, 24⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182071, 7646982, 1205, 11⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6731Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6731Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      118051399505874 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      49569724906768 + secondResidualSingularCeiling := by
  decide

theorem ledger_identifications :
    residualStageOne.regularCountCap =
        ContactMovingParameters6731Research.firstResidualRegularCost ∧
    pivotB.countCap + 1 =
        ContactMovingParameters6731Research.firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap =
        ContactMovingParameters6731Research.secondResidualRegularCost ∧
    pivotGcd12.countCap + 1 =
        ContactMovingParameters6731Research.secondResidualSingularCeiling := by
  decide

end ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6731Research
