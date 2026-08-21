/-
  Defense cut: remaining FRI/proximity slack at the 5313 cert.

  The 5313 certificate already charges
      (5^10 * 262134 + 4) / |𝔽|
  against a 2^{-128} soundness target, with
      𝔽 = KoalaBear.Ext6, |𝔽| = p^6, p = 2^31 - 2^24 + 1.

  Headroom is only 16 bits (factor 107418 ∈ (2^16, 2^17)).
  A t = 33 tallness-puncture would replace 5^10 by 5^33 and
  overflow |𝔽| / 2^128. Puncture-to-tallness is dead; the 5314
  cell must go through n×n MCA minors, not GoodCoeffs det.
-/

namespace ProximityPrize.SubmissionLower.DefenseCut

/-- KoalaBear prime. -/
def p : Nat := 2 ^ 31 - 2 ^ 24 + 1

/-- |KoalaBear.Ext6|. -/
def Fcard : Nat := p ^ 6

/-- MCA+list numerator already charged by `certifiedGammaError_improved_le`. -/
def num10 : Nat := 5 ^ 10 * 262134 + 4

/-- Hypothetical numerator after t = 33 tallness punctures. -/
def num33 : Nat := 5 ^ 33 * 262134 + 4

theorem p_eq : p = 2130706433 := by native_decide
theorem num10_eq : num10 = 2559902343754 := by native_decide

/-- Current 5313 bound really does fit: num10 * 2^128 ≤ |𝔽|. -/
theorem current_fits : num10 * 2 ^ 128 ≤ Fcard := by native_decide

/-- Headroom ≥ 16 bits. -/
theorem slack_ge_16 : num10 * 2 ^ (128 + 16) ≤ Fcard := by native_decide

/-- Headroom < 17 bits. Remaining FRI slack is 16 bits, not 77. -/
theorem slack_lt_17 : Fcard < num10 * 2 ^ (128 + 17) := by native_decide

/-- Integer headroom factor is 107418. -/
theorem headroom_factor : Fcard / (num10 * 2 ^ 128) = 107418 := by native_decide

/-- t = 33 puncture overflows the 2^{-128} budget. -/
theorem puncture_t33_overflows : Fcard < num33 * 2 ^ 128 := by native_decide

/-- Extra 5^{23} cost of replacing 10 punctures by 33 is ~53 bits > 16-bit slack. -/
theorem extra_cost_gt_slack : 2 ^ 17 < 5 ^ 23 := by native_decide

end ProximityPrize.SubmissionLower.DefenseCut
