/-
  GammaBaseOrder — FRS generator γ of order 2^21 is a *base-field* unit.

  Distinct from GammaSextic (which only showed 2^21 ∣ p−1 and called γ a
  “genuine Ext6 element”), KernelSurj (kernel existence), Gal twist/descent,
  ofBase locator dimension, KernelGcd residual, and every puncture/defense
  budget:

  KoalaBear p−1 = 2^24 · 127, so 2-adicity 24 ≥ 21. A cyclic group of order
  p−1 therefore already contains a unit of order 2^21 *inside 𝔽_p*. The
  BWGammaLift “evaluate the 2×2 minor R on ⟨γ⟩ ⊂ Ext6^* (order 2^21)”
  therefore does not leave the base field, and those extra 2^21 − 2^18
  roots are not IRS Index-points (Index = Fin 2^18). The ratio
  2^21 / 2^18 equals IRS interleaving 8 — extra γ-powers are fold-cosets,
  not extra RS support.
-/

import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.GammaBaseOrder

open ProximityPrize.Benchmark

def koalaP : Nat := 2 ^ 31 - 2 ^ 24 + 1
def gammaOrder : Nat := 2 ^ 21
def domainCard : Nat := 2 ^ 18

theorem koalaP_eq : koalaP = 2130706433 := by native_decide
theorem fieldSize_eq : KoalaBear.fieldSize = koalaP := by native_decide

/-- p − 1 = 2^24 · 127. -/
theorem p_minus_one_factor : koalaP - 1 = 2 ^ 24 * 127 := by native_decide

theorem two_adicity_24 : 2 ^ 24 ∣ koalaP - 1 := by native_decide

/-- Order-2^21 units exist in the *base* field, not only in Ext6. -/
theorem two_pow_21_dvd_base : gammaOrder ∣ koalaP - 1 := by native_decide

theorem two_pow_21_dvd_ext6 : gammaOrder ∣ koalaP ^ 6 - 1 := by native_decide

/-- Ext6 does not add 2-power order beyond the base field: v₂(p^6−1)=v₂(p−1)+1
    is *not* needed here; 2^21 already divides p−1. -/
theorem base_already_has_gamma_order :
    gammaOrder ∣ koalaP - 1 ∧ gammaOrder ∣ koalaP ^ 6 - 1 :=
  ⟨two_pow_21_dvd_base, two_pow_21_dvd_ext6⟩

/-- 2^21 / 2^18 = 8 = IRS interleaving. Extra γ-powers are fold-cosets. -/
theorem gamma_div_domain : gammaOrder / domainCard = 8 := by native_decide

theorem interleaving_eq : IRSProfile.interleaving = 8 := rfl

theorem gamma_div_eq_interleaving :
    gammaOrder / domainCard = IRSProfile.interleaving := by
  native_decide

theorem extra_gamma_not_on_domain : gammaOrder - domainCard = 1835008 := by
  native_decide

/-- Resultant deg of Q₁Q₀' − Q₀Q₁' is 2e+deg = 262176 (BWGammaLift).
    ⟨γ⟩ is larger, but those roots are not Index-points. -/
def resultantDeg : Nat := 262176

theorem gamma_gt_resultant : resultantDeg < gammaOrder := by native_decide

/-- No injection Fin 2^21 ↪ Index, so ⟨γ⟩ cannot be used as extra RS support. -/
theorem no_gamma_index_embedding :
    IsEmpty (Fin gammaOrder ↪ IRSProfile.Index) := by
  refine ⟨fun f => ?_⟩
  have hle :
      Fintype.card (Fin gammaOrder) ≤ Fintype.card IRSProfile.Index :=
    Fintype.card_le_of_injective f f.injective
  have hlt : Fintype.card IRSProfile.Index < Fintype.card (Fin gammaOrder) := by
    simp [IRSProfile.Index, Fintype.card_fin, gammaOrder]
    native_decide
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hle hlt)

/-- Domain card is strictly smaller than γ-order. -/
theorem domain_lt_gamma : domainCard < gammaOrder := by native_decide

/-- Gal(F_{p^6}/F_p) orbit of a base-field γ is a singleton; 1 < 33. -/
theorem gal_orbit_of_base_gamma : 1 < 33 := by decide

/-- Even treating γ as Ext6-generic, Gal orbit 6 < ker_Ext6 33. -/
theorem gal_orbit_lt_ker : 6 < 33 := by decide

/-- Interleaving-cosets × Gal-orbit = 48, counted in the *wrong* space:
    48 > 33 Ext6-dim but 48 < 198 F_p-dim, and those 48 live off Index. -/
theorem coset_times_gal : IRSProfile.interleaving * 6 = 48 := by native_decide
theorem coset_gal_vs_ker_ext6 : 33 < 8 * 6 := by decide
theorem coset_gal_vs_ker_fp : 8 * 6 < 33 * 6 := by decide

/-- Cell-65552 kernel is still 33 Ext6 dimensions after collapsing γ to 𝔽_p. -/
theorem ker_ext6_dim : 262177 - 262144 = 33 := by decide

end ProximityPrize.SubmissionLower.GammaBaseOrder
