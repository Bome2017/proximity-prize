import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.TwoKernelCaps

namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 12738110 131071 100000 20 70 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 11464299 131071 100000 18 63 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 8188785 131071 100000 13 45 IRSProfile.domain u0 u1
abbrev ThinKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 8188785 131071 100000 12 45 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 15285732 131071 1420 26 84 IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 70 100000 20 <
    coefficientCount 12738110 131071 100000 20 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelA_nullity
  omega
theorem gateAux : Fintype.card I * localRankBound 63 100000 18 <
    coefficientCount 11464299 131071 100000 18 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelAux_nullity
  omega
theorem gateC : Fintype.card I * localRankBound 45 100000 13 <
    coefficientCount 8188785 131071 100000 13 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelC_nullity
  omega
theorem gateThin : Fintype.card I * localRankBound 45 100000 12 <
    coefficientCount 8188785 131071 100000 12 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelThin_nullity
  omega
theorem gateB : Fintype.card I * localRankBound 84 1420 26 <
    coefficientCount 15285732 131071 1420 26 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelB_nullity
  omega

theorem full_divisor_mem_box (D w L s m : ℕ)
    (gate : Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1 : I → K) (H : P4)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1,
      H ∣ reconstruct K D w L s v.1) :
    H ∈ globalCoefficientBox K D w L s := by
  classical
  have hExists := exists_nonzero_kernel_array (I := I)
    K D w L s m IRSProfile.domain u0 u1 gate
  obtain ⟨a, ha, hk⟩ := hExists
  let v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1 :=
    ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct K D w L s a ≠ 0 := reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd H (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)

theorem full_A_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, H ∣ reconstruct K 12738110 131071 100000 20 v.1) :
    H ∈ globalCoefficientBox K 12738110 131071 100000 20 :=
  full_divisor_mem_box 12738110 131071 100000 20 70 gateA u0 u1 H hdiv

theorem full_Aux_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : AuxKernel u0 u1, H ∣ reconstruct K 11464299 131071 100000 18 v.1) :
    H ∈ globalCoefficientBox K 11464299 131071 100000 18 :=
  full_divisor_mem_box 11464299 131071 100000 18 63 gateAux u0 u1 H hdiv

theorem full_C_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : CKernel u0 u1, H ∣ reconstruct K 8188785 131071 100000 13 v.1) :
    H ∈ globalCoefficientBox K 8188785 131071 100000 13 :=
  full_divisor_mem_box 8188785 131071 100000 13 45 gateC u0 u1 H hdiv

theorem full_Thin_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : ThinKernel u0 u1, H ∣ reconstruct K 8188785 131071 100000 12 v.1) :
    H ∈ globalCoefficientBox K 8188785 131071 100000 12 :=
  full_divisor_mem_box 8188785 131071 100000 12 45 gateThin u0 u1 H hdiv

theorem full_B_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, H ∣ reconstruct K 15285732 131071 1420 26 v.1) :
    H ∈ globalCoefficientBox K 15285732 131071 1420 26 :=
  full_divisor_mem_box 15285732 131071 1420 26 84 gateB u0 u1 H hdiv

theorem common_C_ys_le (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hbox : H ∈ globalCoefficientBox K 8188785 131071 100000 13)
    (hdiv : ∀ v : CKernel u0 u1, H ∣ reconstruct K 8188785 131071 100000 13 v.1) :
    wt residualYSWeights H ≤ 59 := by
  by_contra hnot
  have hy : 60 ≤ wt residualYSWeights H := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H
    8188785 131071 100000 13 (by decide)).mp hbox
  have hr : wt residualSWeights H ≤ 13 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope H 131071 (by decide)
  have hc : 7864247 ≤ wt (contactWeights 131071) H := by omega
  have ht : 60 ≤ wt residualTotalWeights H :=
    hy.trans (residual_weight_nested H).2
  have hdivK : ∀ v : CKernel u0 u1,
      H ∣ kernelReconstructLinear (K := K)
        8188785 131071 100000 13 45 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : CKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          8188785 131071 100000 13 45 IRSProfile.domain u0 u1)
        H hdivK v ∈ globalCoefficientBox K 324538 131071 99940 13 := by
    have h := TwoKernelCaps.quotient_box_of_full_divisor (K := K) (I := I)
      8188785 131071 100000 13 45 7864247 60 0
      IRSProfile.domain u0 u1 H hH hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 8188785 - 7864247 = 324538 by decide,
      show 100000 - 60 = 99940 by decide, Nat.sub_zero] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    8188785 131071 100000 13 45 324538 99940 13
    IRSProfile.domain u0 u1 H hH hdivK hq
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelC_nullity,
    LocatorArithmetic.C_ys60_quotient_upper] at hobs
  omega

theorem common_B_total_le (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, H ∣ reconstruct K 15285732 131071 1420 26 v.1) :
    wt residualTotalWeights H ≤ 1417 := by
  by_contra hnot
  have ht : 1418 ≤ wt residualTotalWeights H := by omega
  have hdivK : ∀ v : BKernel u0 u1,
      H ∣ kernelReconstructLinear (K := K)
        15285732 131071 1420 26 84 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          15285732 131071 1420 26 84 IRSProfile.domain u0 u1)
        H hdivK v ∈ globalCoefficientBox K 15285732 131071 2 26 := by
    have h := TwoKernelCaps.quotient_box_of_full_divisor (K := K) (I := I)
      15285732 131071 1420 26 84 0 1418 0
      IRSProfile.domain u0 u1 H hH hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero, show 1420 - 1418 = 2 by decide] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    15285732 131071 1420 26 84 15285732 2 26
    IRSProfile.domain u0 u1 H hH hdivK hq
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt

end
end ProximityPrize.SubmissionLower.LocatorCaps
