import ProximityPrize.SubmissionLower.FA
namespace ProximityPrize.SubmissionLower.ContactTwoTailClosure6734Research
open ProximityPrize.Benchmark
open ContactTwoTailParameters6734Research
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
theorem alignmentBound6735 :
   AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget := by
 have h := ContactAlignmentBridge.alignmentBound_of_selected_count
   IRSProfile.domain 131071 errors mcaBudget
   ContactTwoTailSelectedBound6734Research.selectedNoLargePencilBound6734
 simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h
theorem protocolClaim6735 : ProtocolClaim 6735 10254463 33554432 :=
 ContactMovingProtocol6734Research.protocolClaim6735_of_alignment
   alignmentBound6735
end
end ProximityPrize.SubmissionLower.ContactTwoTailClosure6734Research
