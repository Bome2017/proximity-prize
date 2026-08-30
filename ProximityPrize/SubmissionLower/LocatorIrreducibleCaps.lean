import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient
import ProximityPrize.SubmissionLower.LocatorSquareWitness


namespace ProximityPrize.SubmissionLower.LocatorIrreducibleCaps

open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN130 RCN156 RCN180 RCN234
open LocatorCaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:CharP K 2130706433:=by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

theorem r11_collar_sum:
    (∑ j∈Finset.range 50,∑ r∈Finset.range 11,
      (95871-j-r)*min 131074 (6518510-131071*j-131070*r))=6181590631194:=by decide
theorem r12_collar_sum:
    (∑ j∈Finset.range 54,∑ r∈Finset.range 10,
      (95875-j-r)*min 131074 (7042795-131071*j-131070*r))=6185092702940:=by decide
theorem r13_collar_sum:
    (∑ j∈Finset.range 58,∑ r∈Finset.range 9,
      (95879-j-r)*min 131074 (7567080-131071*j-131070*r))=6075525789948:=by decide
theorem thin_r10_collar_sum:
    (∑ j∈Finset.range 56,∑ r∈Finset.range 15,
      (18230-j-r)*min 131074 (7267966-131071*j-131070*r))=1733668273220:=by decide
theorem b_r10_collar_sum:
    (∑ j∈Finset.range 111,∑ r∈Finset.range 18,
      (37-j-r)*min 131074 (14520081-131071*j-131070*r))=1023556866:=by decide
theorem b_r11_collar_sum:
    (∑ j∈Finset.range 110,∑ r∈Finset.range 17,
      (37-j-r)*min 131074 (14389011-131071*j-131070*r))=996031326:=by decide
theorem b_r12_collar_sum:
    (∑ j∈Finset.range 109,∑ r∈Finset.range 16,
      (37-j-r)*min 131074 (14257941-131071*j-131070*r))=965753232:=by decide
theorem b_r13_collar_sum:
    (∑ j∈Finset.range 108,∑ r∈Finset.range 15,
      (38-j-r)*min 131074 (14126871-131071*j-131070*r))=993540920:=by decide


private theorem rank_le_small_sum
    (D L s m:ℕ) (hm:1≤m)
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1,
      F∣reconstruct K D 131071 L s v.1)
    (hpos:0<F.degreeOf (2:Fin 4))
    (hlt:F.degreeOf (2:Fin 4)<2130706433)
    (hhalf:s<2*F.degreeOf (2:Fin 4))
    (Dcap Lcap qcap J:ℕ)
    (hD:D - wt (contactWeights 131071) F≤Dcap)
    (hL:L - wt residualTotalWeights F≤Lcap)
    (hq:s - wt residualSWeights F≤qcap)
    (hJ:Dcap≤131071*J):
    Module.finrank K
        (ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1)≤
      ∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
        (Lcap+1 - j - r)*
          min 131074 (Dcap - 131071*j - 131070*r):=by
  have hzero:∀
      (v:ConstraintKernel (K:=K) D 131071 L s m IRSProfile.domain u0 u1) (P:P4),
      reconstruct K D 131071 L s v.1=F*P →
      P∈globalCoefficientBox K
        (D - wt (contactWeights 131071) F - 131074) 131071
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P=0:=by
    intro v P hprod hprefix
    exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
      D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1
      F hF hdiv hpos hlt hhalf hm
      (by norm_num [I,IRSProfile.Index]) v P hprod hprefix
  have h:=LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
    D 131071 L s m 131074 IRSProfile.domain u0 u1
    F hF.ne_zero hdiv hzero Dcap Lcap qcap J hD hL hq hJ
  simpa only [show 131071 - 1=131070 by decide] using h

private theorem aux_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:AuxKernel u0 u1,
      F∣reconstruct K 13465262 131071 95923 21 v.1)
    (R ycap Dcap Lcap qcap J upper:ℕ)
    (hR:F.degreeOf (2:Fin 4)=R) (hY:ycap≤wt residualYSWeights F)
    (hRpos:0<R) (hRchar:R<2130706433) (hhalf:21<2*R)
    (hDnum:13465262 - (131071*ycap - R)≤Dcap)
    (hLnum:95923 - ycap≤Lcap) (hqnum:21 - R≤qcap)
    (hJnum:Dcap≤131071*J)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hlt:upper<6185093728418):False:=by
  have hRwt:wt residualSWeights F=R:=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hm:=Nat.mul_le_mul_left 131071 hY
  have hc:131071*ycap - R≤wt (contactWeights 131071) F:=by omega
  have ht:=hY.trans (residual_weight_nested F).2
  have hD:13465262 - wt (contactWeights 131071) F≤Dcap:=
    (Nat.sub_le_sub_left hc _).trans hDnum
  have hL:95923 - wt residualTotalWeights F≤Lcap:=
    (Nat.sub_le_sub_left ht _).trans hLnum
  have hq:21 - wt residualSWeights F≤qcap:=by omega
  have hu:=rank_le_small_sum 13465262 95923 21 74 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; exact hRpos) (by rw [hR]; exact hRchar)
    (by rw [hR]; exact hhalf)
    Dcap Lcap qcap J hD hL hq hJnum
  rw [hsum] at hu
  have hl:=constraintKernel_finrank_lower_bound (K:=K)
    13465262 131071 95923 21 74 IRSProfile.domain u0 u1
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelAux_nullity] at hl
  omega

theorem full_A_r11_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:AuxKernel u0 u1,F∣reconstruct K 13465262 131071 95923 21 v.1)
    (hR:F.degreeOf (2:Fin 4)=11):wt residualYSWeights F≤52:=by
  by_contra h
  exact aux_factor_ys_le u0 u1 F hF hdiv 11 53 6518510 95870 10 50
    6181590631194 hR (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    r11_collar_sum (by decide)

theorem full_A_r12_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:AuxKernel u0 u1,F∣reconstruct K 13465262 131071 95923 21 v.1)
    (hR:F.degreeOf (2:Fin 4)=12):wt residualYSWeights F≤48:=by
  by_contra h
  exact aux_factor_ys_le u0 u1 F hF hdiv 12 49 7042795 95874 9 54
    6185092702940 hR (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    r12_collar_sum (by decide)

theorem full_A_r13_factor_ys_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:AuxKernel u0 u1,F∣reconstruct K 13465262 131071 95923 21 v.1)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualYSWeights F≤44:=by
  by_contra h
  exact aux_factor_ys_le u0 u1 F hF hdiv 13 45 7567080 95878 8 58
    6075525789948 hR (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    r13_collar_sum (by decide)

theorem full_Aux_r10_factor_ys_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:ThinKernel u0 u1,
      F∣reconstruct K 14739003 131071 18286 24 v.1)
    (hR:F.degreeOf (2:Fin 4)=10):wt residualYSWeights F≤56:=by
  apply LocatorSquareWitness.factor_ys_le_of_square_collar
    14739003 131071 18286 24 81 131074 2130706433 10 56 112
    7267966 18229 14 56 IRSProfile.domain u0 u1 F hF hdiv hR
    (by decide) (by decide) (by decide) (by decide) (by norm_num [I,IRSProfile.Index])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro Q hQ hbox
    have hc:=((mem_flagGlobalCoefficientBox_iff Q 14739003 131071 18286 24
      (by decide)).mp hbox).2.2
    have hs:=((mem_flagGlobalCoefficientBox_iff Q 14739003 131071 18286 24
      (by decide)).mp hbox).2.1
    have hy:=residualYS_mul_le_contact_add_slope Q 131071 (by decide)
    omega
  · rw [show 14+1=15 by decide,show 18229+1=18230 by decide,
      thin_r10_collar_sum,show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
      LocatorArithmetic.kernelThin_nullity]
    decide

private theorem b_factor_total_le
    (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1)
    (R cap Dcap Lcap qcap J upper:ℕ) (hR:F.degreeOf (2:Fin 4)=R)
    (hRpos:0<R) (hRchar:R<2130706433)
    (hsum:(∑ j∈Finset.range J,∑ r∈Finset.range (qcap+1),
      (Lcap+1-j-r)*min 131074 (Dcap-131071*j-131070*r))=upper)
    (hnum:upper<1028848471) (hD:15830781-(131071*R-R)≤Dcap)
    (hL:1451-(cap+1)≤Lcap) (hq:27-R≤qcap)
    (hJ:Dcap≤131071*J) (hsq:1451<2*(cap+1)):
    wt residualTotalWeights F≤cap:=by
  apply LocatorSquareWitness.factor_total_le_of_square_collar
    15830781 131071 1451 27 87 131074 2130706433 R cap
    Dcap Lcap qcap J IRSProfile.domain u0 u1 F hF hdiv hR
    hRpos hRchar (by decide) (by decide) (by decide)
    (by norm_num [I,IRSProfile.Index]) hD hL hq hJ hsq
  rw [hsum,show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelB_nullity]
  exact hnum

theorem full_B_r10_factor_total_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=10):wt residualTotalWeights F≤1414:=
  b_factor_total_le u0 u1 F hF hdiv 10 1414 14520081 36 17 111 1023556866
    hR (by decide) (by decide) b_r10_collar_sum (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem full_B_r11_factor_total_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=11):wt residualTotalWeights F≤1414:=
  b_factor_total_le u0 u1 F hF hdiv 11 1414 14389011 36 16 110 996031326
    hR (by decide) (by decide) b_r11_collar_sum (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem full_B_r12_factor_total_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=12):wt residualTotalWeights F≤1414:=
  b_factor_total_le u0 u1 F hF hdiv 12 1414 14257941 36 15 109 965753232
    hR (by decide) (by decide) b_r12_collar_sum (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem full_B_r13_factor_total_le (u0 u1:I → K) (F:P4) (hF:Irreducible F)
    (hdiv:∀ v:BKernel u0 u1,F∣reconstruct K 15830781 131071 1451 27 v.1)
    (hR:F.degreeOf (2:Fin 4)=13):wt residualTotalWeights F≤1413:=
  b_factor_total_le u0 u1 F hF hdiv 13 1413 14126871 37 14 108 993540920
    hR (by decide) (by decide) b_r13_collar_sum (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
