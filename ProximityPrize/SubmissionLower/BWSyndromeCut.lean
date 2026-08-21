/-
BW-syndrome defense cut (new edge, not tallness N−n and not 5^k/2^k extra punctures).

Prior defense files compared extra-row *puncture* cost against FRI slack:
  ExtraPunctureBudget : 5-ary budget 7  <  tallness 33
  BinaryPunctureCut   : binary budget 16 <  tallness 33

This file asks a different question, using the BW/GoodCoeffs quantity already
computed at cell 65552 in HBaseMCA.lean:

    2*e − deg = 32

If instantiating the Berlekamp–Welch / GoodCoeffs kernel at this cell requires
covering those 32 syndrome rows, does the measured 16-bit |𝔽|/num10 headroom
pay for them — even at 1 bit per syndrome (binary), let alone 5-ary?

Constants match BinaryPunctureCut / ExtraPunctureBudget / DefenseCut:
  num10 = 2559902343754  (5^10 * 262134 + 4, the 5313 puncture numerator)
  |𝔽|   = p^6
  slack: num10 * 2^144 ≤ |𝔽| < num10 * 2^145
-/

def p : Nat := 2013265921
def Fcard : Nat := p ^ 6
def num10 : Nat := 2559902343754
def twoEminusDeg : Nat := 32

/-- Reconfirm the 16-bit slack window. -/
theorem slack_lo : num10 * 2 ^ 144 ≤ Fcard := by native_decide
theorem slack_hi : Fcard < num10 * 2 ^ 145 := by native_decide

/-- Binary extra-row budget is 16 (same as BinaryPunctureCut). -/
theorem binary_16_fits : num10 * 2 ^ 16 * 2 ^ 128 ≤ Fcard := by native_decide
theorem binary_17_overflows : Fcard < num10 * 2 ^ 17 * 2 ^ 128 := by native_decide

/-- 16 < 2*e − deg. Binary budget cannot cover BW syndrome width. -/
theorem binary_budget_lt_bw_syndrome : 16 < twoEminusDeg := by native_decide

/-- Even 1-bit-per-syndrome (2^{32}) overflows |𝔽|. -/
theorem bw_syndrome_32_overflows :
    Fcard < num10 * 2 ^ twoEminusDeg * 2 ^ 128 := by native_decide

/-- 5-ary extra-puncture budget is 7 (ExtraPunctureBudget); 7 < 32. -/
theorem five_ary_budget_lt_bw_syndrome : 7 < twoEminusDeg := by native_decide

/-- Combined: BW-syndrome rows cannot be paid from remaining FRI slack. -/
theorem bw_syndrome_binary_closed :
    16 < twoEminusDeg ∧ Fcard < num10 * 2 ^ twoEminusDeg * 2 ^ 128 :=
  ⟨binary_budget_lt_bw_syndrome, bw_syndrome_32_overflows⟩
