/-
  Extra-puncture budget under the 16-bit FRI slack of the 5313 cert.

  Distinct from:
    (1) charging 5^t against a 2^128 numerator cap
    (2) charging 5^33 (tallness) against |𝔽|/num10 headroom

  Question answered here: how many *extra* punctures beyond P.card = 10
  still satisfy 5^k * num10 * 2^128 ≤ |𝔽|?

  Headroom factor is 107418 ∈ (2^16, 2^17), and
    5^7 = 78125 < 107418 < 390625 = 5^8,
  so the extra-puncture budget is 7 (total P.card ≤ 17), not 33.
  Cell 65552 still needs N − n = 33 extra rows, so GoodCoeffs-det via
  puncture-to-tallness stays closed. This is the precise remaining FRI cut.
-/

namespace ProximityPrize.SubmissionLower.ExtraPunctureBudget

/-- KoalaBear prime `p = 2^31 − 2^24 + 1`. -/
def p : Nat := 2 ^ 31 - 2 ^ 24 + 1

/-- `|𝔽| = p^6` (KoalaBear.Ext6). -/
def Fcard : Nat := p ^ 6

/-- Numerator of the 5313 proximity charge at `P.card = 10`. -/
def num10 : Nat := 2559902343754

/-- Extra 7 punctures still fit in the 16-bit slack. -/
theorem extra_punc_7_fits : 5 ^ 7 * num10 * 2 ^ 128 ≤ Fcard := by
  native_decide

/-- Extra 8 punctures overflow the 16-bit slack. -/
theorem extra_punc_8_overflows : Fcard < 5 ^ 8 * num10 * 2 ^ 128 := by
  native_decide

/-- Cell 65552 tallness gap is 33 extra rows; extra budget 7 < 33. -/
theorem extra_budget_lt_tallness_gap : 7 < 33 := by
  decide

end ProximityPrize.SubmissionLower.ExtraPunctureBudget
