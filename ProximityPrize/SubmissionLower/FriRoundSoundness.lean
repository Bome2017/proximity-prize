/-
FRI 18-round fold-product soundness of the 33-dim BW kernel.

Distinct from:
  * 5^t puncture vs 2^128 (DefenseCut)
  * 5^t vs |𝔽|/num10
  * extra-puncture budget k
  * 2^k extra-row tallness vs excess 33 (BinaryPunctureCut)
  * IRS interleave-8 fold of the kernel (FoldKernel)

Binary FRI on Index = ⟨ω⟩ ⊂ 𝔽_p, |Index| = n = 2^18, performs exactly
18 domain-halving folds. Charging the identification cost as 2^{rounds}
= 2^18 = n, not as an RS-list union 5^{excess} = 5^33, is the defense
cut: 2^18 ≪ 5^33 ≪ 2^128, so fold-depth charging fits the remaining
bit budget where a 33-puncture 5-ary union does not.

The leftover ray after peeling 16 fold-pairs off the 33-dim kernel is
the unique-decoding excess (33 = 1 + 2·16, 33 odd). That odd ray is
why a pure fold-even subspace cannot swallow the kernel; the soundness
product is still 18 binary folds, not 33 quinary punctures.

This file is an arithmetic gate. It does not instantiate ProtocolClaim
(`N > n` still blocks GoodCoeffs).
-/

import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.FriRoundSoundness

def n : Nat := 262144
def e : Nat := 65552
def excess : Nat := 33
def folds : Nat := 18
def extraErrors : Nat := 16
def koala : Nat := 2 ^ 24 * 127 + 1

theorem n_pow : (2 : Nat) ^ folds = n := by native_decide

theorem koala_p : koala = 2130706433 := by native_decide

theorem excess_odd : excess % 2 = 1 := by native_decide

/-- Unique-decoding excess 1 plus 16 fold-pairs (the 16 errors past tUnique). -/
theorem excess_split : 1 + 2 * extraErrors = excess := by native_decide

/-- Binary fold-depth cost equals the evaluation support. -/
theorem fold_cost_eq_n : (2 : Nat) ^ folds = n := n_pow

/-- 5-ary list-union at the 33-dim excess is strictly heavier than 18 folds. -/
theorem fold_cost_lt_list_cost : (2 : Nat) ^ folds < 5 ^ excess := by native_decide

/-- 33-puncture 5-ary union still fits inside a 128-bit numerator, but
    eats ~76.6 of those bits (open lead: ≥77-bit slack?). Fold-depth
    eats only 18. -/
theorem list_cost_lt_128 : (5 : Nat) ^ excess < 2 ^ 128 := by native_decide

theorem fold_cost_lt_128 : (2 : Nat) ^ folds < 2 ^ 128 := by native_decide

/-- Headroom if the cert charges 2^{18} instead of 5^{33} against 2^{128}. -/
theorem fold_headroom : 2 ^ 128 / (2 : Nat) ^ folds = 2 ^ 110 := by native_decide

/-- Headroom if the cert still charges 5^{33} against 2^{128}.
    2^128 / 5^33 is not a pure power of two; we only record the
    inequality 2^51 < 2^128/5^33 < 2^52. -/
theorem list_headroom_lo : (2 : Nat) ^ 51 * 5 ^ excess < 2 ^ 128 := by native_decide

theorem list_headroom_hi : (2 : Nat) ^ 128 < 2 ^ 52 * 5 ^ excess := by native_decide

/-- Cell e sits 16 past unique decoding; those 16 errors are 32 BW
    columns = 16 binary fold-pairs, not 16 extra FRI rounds. -/
theorem extra_is_pairs_not_rounds : 2 * extraErrors = 32 ∧ extraErrors < folds := by
  native_decide

/-- KoalaBear 2-adic valuation: p−1 = 2^{24}·127, so 18 folds sit
    strictly inside the 2-Sylow (24−18 = 6 leftover doubling bits).
    The IRS interleave is the *other* 2-power 2^{21}/2^{18} = 2^3 = 8,
    not 2^6. -/
theorem sylow_leftover : 24 - folds = 6 ∧ 2 ^ 3 = 8 := by native_decide

end ProximityPrize.SubmissionLower.FriRoundSoundness
