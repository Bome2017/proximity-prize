/-
Binary-puncture defense cut (new edge, not 5^t).

Prior defense directions charged 5^k extra punctures against FRI slack.
This file asks the weaker question: even if each extra row cost only a
*binary* factor 2 (not 5), can 33 tallness-rows fit in the measured
16-bit |𝔽|/num10 headroom?

Constants match ExtraPunctureBudget / DefenseCut:
  num10 = 2559902343754  (5^10 * 262134 + 4, the 5313 puncture numerator)
  |𝔽|   = p^6            (BabyBear extension used by the cert)
  slack: num10 * 2^144 ≤ |𝔽| < num10 * 2^145
-/

def p : Nat := 2013265921
def Fcard : Nat := p ^ 6
def num10 : Nat := 2559902343754

/-- Reconfirm the 16-bit slack window on this p. -/
theorem slack_lo : num10 * 2 ^ 144 ≤ Fcard := by native_decide
theorem slack_hi : Fcard < num10 * 2 ^ 145 := by native_decide

/-- 16 extra *binary* factors still fit (matches 2^144 bound). -/
theorem binary_16_fits : num10 * 2 ^ 16 * 2 ^ 128 ≤ Fcard := by native_decide

/-- 17 extra binary factors overflow. Binary extra-row budget is exactly 16. -/
theorem binary_17_overflows : Fcard < num10 * 2 ^ 17 * 2 ^ 128 := by native_decide

/-- Tallness gap at cell 65552 is 33 rows; 16 < 33. -/
theorem binary_budget_lt_tallness : 16 < 33 := by native_decide

/-- Even 2^33 extra (one bit per tallness row) overflows |𝔽|. -/
theorem binary_33_overflows : Fcard < num10 * 2 ^ 33 * 2 ^ 128 := by native_decide

/-- Combined: binary puncture cannot close N−n = 33. -/
theorem binary_puncture_to_tallness_closed :
    16 < 33 ∧ Fcard < num10 * 2 ^ 33 * 2 ^ 128 :=
  ⟨binary_budget_lt_tallness, binary_33_overflows⟩
