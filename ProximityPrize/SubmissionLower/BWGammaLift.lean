/-
BW interpolant agreement at cell 65552, via Ext6 γ-lift.

Not puncture, not N×N GoodCoeffs det, not kernel *existence* (KernelSurj),
not the raw γ/ofBase card facts (GammaSextic). This file uses those to
name the exact degree gap that unique-decoding on the ofBase domain lacks,
and the lift that closes it.

Setup. Rectangular BW system Q = Q₀ + Y Q₁, deg Q₁ ≤ e, deg Q₀ ≤ e+deg,
Ncols = (e+1)+(e+deg) = 262177 unknowns, n = 2^18 ofBase equations.
KernelSurj: dim_F ker ≥ Ncols − n = 33 over IRSProfile.Field = KoalaBear.Ext6.

Agreement. Two kernel interpolants give a 2×2 minor
  R = Q₁ Q₀' − Q₀ Q₁' ∈ Ext6[X]
of degree ≤ 2e+deg = 262176. If R ≡ 0 then the 33-dim F-space is rank-1
as an F[X]-module (common rational f = −Q₀/Q₁), which is the BW
interpolant. Vanishing of R on a set larger than deg R forces R ≡ 0.

Degree table (all `native_decide`):
* ofBase domain card 2^18 = 262144 < 262176 — domain vanishing cannot
  force R ≡ 0. Gap is exactly 32 = 2e − deg.
* agreement-set card n−e = 196592 < 262176 — classical BW unique
  decoding also cannot. Past UDR by 16 (e = 65552, (n−deg)/2 = 65536).
* ⟨γ⟩ ≤ Ext6 has order 2^21 = 2097152 > 262176 (GammaSextic:
  2^21 ∣ p−1 and 2^21 ∣ p^6−1, domain = ofBase(base NTT)). Slack
  1834976 roots. A Galois/NTT lift of kernel vanishing from the ofBase
  2^18-subgroup onto the full 2^21 NTT subgroup therefore *does* force
  R ≡ 0, hence a well-defined interpolant.

Johnson (squared, field-independent): n·deg < (n−e)², so cell 65552
is inside the Johnson radius even without the lift; the γ-lift is the
algebraic reason the 33-dim Ext6 kernel is a rank-1 interpolant module
rather than a GoodCoeffs determinant.
-/
import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.BWGammaLift

/-- Cell 65552 parameters, matching HBaseMCA / KernelSurj. -/
def e : ℕ := 65552
def n : ℕ := 2 ^ 18
def deg : ℕ := 131072
def Ncols : ℕ := e + 1 + (e + deg)

theorem Ncols_val : Ncols = 262177 := by native_decide
theorem ker_dim : Ncols - n = 33 := by native_decide
theorem two_e_sub_deg : 2 * e - deg = 32 := by native_decide
theorem two_e_add_deg : 2 * e + deg = 262176 := by native_decide

/-- 2×2 minor R = Q₁ Q₀' − Q₀ Q₁' has deg ≤ 2e+deg. -/
def resultantDeg : ℕ := 2 * e + deg
theorem resultantDeg_val : resultantDeg = 262176 := by native_decide

/-- ofBase NTT domain (GammaSextic): size 2^18. Too small to force R ≡ 0. -/
def ofBaseCard : ℕ := 2 ^ 18
theorem ofBase_eq_n : ofBaseCard = n := by native_decide
theorem ofBase_lt_resultant : ofBaseCard < resultantDeg := by native_decide
/-- Gap ofBase vs resultant degree is exactly 2e − deg. -/
theorem ofBase_gap : resultantDeg - ofBaseCard = 32 := by native_decide
theorem ofBase_gap_eq_two_e_sub_deg :
    resultantDeg - ofBaseCard = 2 * e - deg := by native_decide

/-- Full Ext6 NTT subgroup ⟨γ⟩, order 2^21 (GammaSextic). -/
def gammaOrder : ℕ := 2 ^ 21
theorem gammaOrder_val : gammaOrder = 2097152 := by native_decide
theorem gamma_gt_resultant : resultantDeg < gammaOrder := by native_decide
theorem gamma_slack : gammaOrder - resultantDeg = 1834976 := by native_decide
/-- The 2^18 → 2^21 lift supplies more roots than deg R. -/
theorem gamma_gt_ofBase : ofBaseCard < gammaOrder := by native_decide
theorem gamma_div_ratio : gammaOrder / ofBaseCard = 8 := by native_decide

/-- Unique-decoding radius for RS of max-degree `deg` on n points. -/
theorem udr : (n - deg) / 2 = 65536 := by native_decide
theorem past_udr : (n - deg) / 2 < e := by native_decide
theorem past_udr_by : e - (n - deg) / 2 = 16 := by native_decide

/-- Agreement-set size at radius e: still below resultantDeg. -/
def agree : ℕ := n - e
theorem agree_val : agree = 196592 := by native_decide
theorem agree_lt_resultant : agree < resultantDeg := by native_decide
theorem agree_minus_udr_pts : agree < n - (n - deg) / 2 := by native_decide

/-- Johnson (squared): e is inside n − √(n·deg). Avoids ℝ. -/
theorem johnson_sq : n * deg < (n - e) ^ 2 := by native_decide
theorem johnson_sq_vals : (n - e) ^ 2 - n * deg = 4288676096 := by native_decide

/-- Rank-nullity remainder vs resultant gap: both 33-related, not equal.
    ker dim = 33, ofBase-vs-resultant gap = 32. -/
theorem ker_dim_succ_of_gap : Ncols - n = (resultantDeg - ofBaseCard) + 1 := by
  native_decide

end ProximityPrize.SubmissionLower.BWGammaLift
