import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleContact
import ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient

/-!
The A70 and auxiliary A63 bounds apply to irreducible
whole-kernel divisors.
They are factorwise bounds, not bounds on a possibly reducible whole gcd.
The actual weighted, total, and R degree differences are retained until
the final finite-coordinate embedding.
-/
namespace ProximityPrize.SubmissionLower.LocatorIrreducibleCaps

open scoped BigOperators
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN130 RCN156 RCN180 RCN234
open LocatorCaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 2048

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K 2130706433 := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

theorem r13_collar_sum :
    (∑ j ∈ Finset.range 51, ∑ r ∈ Finset.range 8,
      (99954 - j - r) * min 131074 (6576386 - 131071 * j - 131070 * r)) =
        4890686735920 := by decide

theorem r12_collar_sum :
    (∑ j ∈ Finset.range 46, ∑ r ∈ Finset.range 9,
      (99949 - j - r) * min 131074 (5921030 - 131071 * j - 131070 * r)) =
        4853542426374 := by decide

theorem r11_collar_sum :
    (∑ j ∈ Finset.range 43, ∑ r ∈ Finset.range 10,
      (99946 - j - r) * min 131074 (5527816 - 131071 * j - 131070 * r)) =
        4934324508280 := by decide

theorem r10_collar_sum :
    (∑ j ∈ Finset.range 29, ∑ r ∈ Finset.range 9,
      (99942 - j - r) * min 131074 (3729860 - 131071 * j - 131070 * r)) =
        2882963457372 := by decide

/-- The abstract collar bound is supplied with the proved irreducible
low-prefix exclusion, rather than with an independent rank hypothesis. -/
private theorem rank_le_small_sum
    (D L s m : ℕ) (hm : 1 ≤ m)
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D 131071 L s v.1)
    (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hlt : F.degreeOf (2 : Fin 4) < 2130706433)
    (hhalf : s < 2 * F.degreeOf (2 : Fin 4))
    (Dcap Lcap qcap J : ℕ)
    (hD : D - wt (contactWeights 131071) F ≤ Dcap)
    (hL : L - wt residualTotalWeights F ≤ Lcap)
    (hq : s - wt residualSWeights F ≤ qcap)
    (hJ : Dcap ≤ 131071 * J) :
    Module.finrank K
        (ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1) ≤
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
        (Lcap + 1 - j - r) *
          min 131074 (Dcap - 131071 * j - 131070 * r) := by
  have hzero : ∀
      (v : ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1) (P : P4),
      reconstruct K D 131071 L s v.1 = F * P →
      P ∈ globalCoefficientBox K
        (D - wt (contactWeights 131071) F - 131074) 131071
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P = 0 := by
    intro v P hprod hprefix
    exact LocatorIrreducibleContact.irreducible_half_slope_quotient_eq_zero_of_mem_prefix
      D 131071 L s m 131074 2130706433 IRSProfile.domain u0 u1
      F hF hdiv hpos hlt hhalf hm
      (by norm_num [I, IRSProfile.Index]) v P hprod hprefix
  have h := LocatorMultiSlopeQuotient.whole_kernel_finrank_le_small_sum
    D 131071 L s m 131074 IRSProfile.domain u0 u1
    F hF.ne_zero hdiv hzero Dcap Lcap qcap J hD hL hq hJ
  simpa only [show 131071 - 1 = 131070 by decide] using h

/-- An irreducible R13 factor dividing the entire A70 kernel has YS<=46. -/
theorem full_A_r13_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736710 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 13) :
    wt residualYSWeights F ≤ 46 := by
  by_contra hnot
  have hYS : 47 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 13 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 6160324 ≤ wt (contactWeights 131071) F := by omega
  have ht : 47 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736710 - wt (contactWeights 131071) F ≤ 6576386 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99953 := by omega
  have hq : 20 - wt residualSWeights F ≤ 7 := by omega
  have hupper := rank_le_small_sum 12736710 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    6576386 99953 7 51 hD hL hq (by decide)
  simp only [show 7 + 1 = 8 by decide, show 99953 + 1 = 99954 by decide,
    r13_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4890686735920 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736710 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4953442449347 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- An irreducible R12 factor dividing the entire A70 kernel has YS<=51. -/
theorem full_A_r12_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736710 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 12) :
    wt residualYSWeights F ≤ 51 := by
  by_contra hnot
  have hYS : 52 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 12 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 6815680 ≤ wt (contactWeights 131071) F := by omega
  have ht : 52 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736710 - wt (contactWeights 131071) F ≤ 5921030 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99948 := by omega
  have hq : 20 - wt residualSWeights F ≤ 8 := by omega
  have hupper := rank_le_small_sum 12736710 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    5921030 99948 8 46 hD hL hq (by decide)
  simp only [show 8 + 1 = 9 by decide, show 99948 + 1 = 99949 by decide,
    r12_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4853542426374 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736710 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4953442449347 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- An irreducible R11 factor dividing the entire A70 kernel has YS<=54. -/
theorem full_A_r11_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 12736710 131071 100000 20 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 11) :
    wt residualYSWeights F ≤ 54 := by
  by_contra hnot
  have hYS : 55 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 11 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 7208894 ≤ wt (contactWeights 131071) F := by omega
  have ht : 55 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 12736710 - wt (contactWeights 131071) F ≤ 5527816 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99945 := by omega
  have hq : 20 - wt residualSWeights F ≤ 9 := by omega
  have hupper := rank_le_small_sum 12736710 100000 20 70 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    5527816 99945 9 43 hD hL hq (by decide)
  simp only [show 9 + 1 = 10 by decide, show 99945 + 1 = 99946 by decide,
    r11_collar_sum] at hupper
  change Module.finrank K (AKernel u0 u1) ≤ 4934324508280 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    12736710 131071 100000 20 70 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity] at hlower
  change 4953442449347 ≤ Module.finrank K (AKernel u0 u1) at hlower
  omega

/-- The auxiliary A63 kernel gives the R10 factor bound YS<=58. -/
theorem full_Aux_r10_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : Irreducible F)
    (hdiv : ∀ v : AuxKernel u0 u1,
      F ∣ reconstruct K 11463039 131071 100000 18 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 10) :
    wt residualYSWeights F ≤ 58 := by
  by_contra hnot
  have hYS : 59 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 10 :=
    (LocatorContact.slope_weight_eq_degreeR F).trans hR
  have hweighted := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 7733179 ≤ wt (contactWeights 131071) F := by omega
  have ht : 59 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2
  have hD : 11463039 - wt (contactWeights 131071) F ≤ 3729860 := by omega
  have hL : 100000 - wt residualTotalWeights F ≤ 99941 := by omega
  have hq : 18 - wt residualSWeights F ≤ 8 := by omega
  have hupper := rank_le_small_sum 11463039 100000 18 63 (by decide) u0 u1 F hF hdiv
    (by rw [hR]; decide) (by rw [hR]; decide) (by rw [hR]; decide)
    3729860 99941 8 29 hD hL hq (by decide)
  simp only [show 8 + 1 = 9 by decide, show 99941 + 1 = 99942 by decide,
    r10_collar_sum] at hupper
  change Module.finrank K (AuxKernel u0 u1) ≤ 2882963457372 at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    11463039 131071 100000 18 63 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelAux_nullity] at hlower
  change 2948801310715 ≤ Module.finrank K (AuxKernel u0 u1) at hlower
  omega

end
end ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
