import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingFixedSelected6731Research
import ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6731Research
import ProximityPrize.SubmissionLower.ContactMovingProtocol6731Research

/-! Premise-free assembly of the fixed cell, stacked residual cells, and protocol. -/
namespace ProximityPrize.SubmissionLower.ContactMovingClosure6731Research

open ProximityPrize.Benchmark
open ContactMovingFixedProfile6731Research
open ContactMovingFixedSelected6731Research
open ContactMovingStackedSelectedBound6731Research

noncomputable section
set_option maxRecDepth 30000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem fixedCellCountProvider6731 : FixedCellCountProvider6731 := by
  intro Q hQ hbox Hsupport selected Δ u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field prime := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_characteristic6600
  have h := fixed_selected_count_le Q hQ hbox Hsupport selected Δ
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree hsolution hagreement hnoPencil
  simpa [ContactMovingParameters6731Research.fixedCost] using h

theorem alignmentBound6731 :
    AffineLineAlignmentBound IRSProfile.baseCode 80073 274980727111395087 := by
  have h := ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain 131071 80073 274980727111395087
    (selectedNoLargePencilBound6731_of_fixedProvider fixedCellCountProvider6731)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem protocolClaim6731 : ProtocolClaim 6731 320295 1048576 :=
  ContactMovingProtocol6731Research.protocolClaim6731_of_alignment alignmentBound6731

#print axioms protocolClaim6731

end
end ProximityPrize.SubmissionLower.ContactMovingClosure6731Research
