import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
import ProximityPrize.SubmissionLower.AB



namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_C_flag {u0 u1:I → K} (S:SelectedPair u0 u1):
    gcd S.QA S.QB∈globalCoefficientBox K 8188335 131071 100000 13:=
  LocatorCaps.full_C_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_Thin_flag {u0 u1:I → K} (S:SelectedPair u0 u1):
    gcd S.QA S.QB∈globalCoefficientBox K 14739003 131071 18286 24:=
  LocatorCaps.full_Thin_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_Thin

theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualTotalWeights (gcd S.QA S.QB)≤1445:=
  LocatorCaps.common_B_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualYSWeights (gcd S.QA S.QB)≤59:=
  LocatorCaps.common_C_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_C_flag S.common_divides_C

theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualSWeights (gcd S.QA S.QB)≤13:=
  ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
    8188335 131071 100000 13 (by decide)).mp S.common_C_flag).2.1

theorem common_degreeR_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    (gcd S.QA S.QB).degreeOf (2:Fin 4)≤13:=by
  simpa only [LocatorContact.slope_weight_eq_degreeR] using S.common_slope_le

theorem factor_r12_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=12):
    wt residualYSWeights F≤48:=by
  have hdivH:F∣gcd S.QA S.QB:=by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r12_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_Aux v)

theorem factor_r11_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=11):
    wt residualYSWeights F≤52:=by
  have hdivH:F∣gcd S.QA S.QB:=by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r11_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_Aux v)

theorem factor_r10_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=10):
    wt residualYSWeights F≤56:=by
  have hdivH:F∣gcd S.QA S.QB:=by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_Aux_r10_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_Thin v)

theorem factor_r13_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualYSWeights F≤44:=by
  have hdivH:F∣gcd S.QA S.QB:=by simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r13_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_Aux v)

private theorem factor_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hdiv:F∣RCN259.gcd12 S.QA S.QB):
    ∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1:=by
  intro v
  have hdivH:F∣gcd S.QA S.QB:=by simpa only [RCN259.gcd12] using hdiv
  exact hdivH.trans (S.common_divides_B v)

theorem factor_r10_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=10):wt residualTotalWeights F≤1414:=
  LocatorIrreducibleCaps.full_B_r10_factor_total_le u0 u1 F hF
    (factor_total_le S F hdiv) hR
theorem factor_r11_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=11):wt residualTotalWeights F≤1414:=
  LocatorIrreducibleCaps.full_B_r11_factor_total_le u0 u1 F hF
    (factor_total_le S F hdiv) hR
theorem factor_r12_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=12):wt residualTotalWeights F≤1414:=
  LocatorIrreducibleCaps.full_B_r12_factor_total_le u0 u1 F hF
    (factor_total_le S F hdiv) hR
theorem factor_r13_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualTotalWeights F≤1413:=
  LocatorIrreducibleCaps.full_B_r13_factor_total_le u0 u1 F hF
    (factor_total_le S F hdiv) hR

end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
