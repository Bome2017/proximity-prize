/-
HBase MCA kernel at the 5314 cell (e = 65552).

Defense cut, distinct from RelUDR / e+deg ≤ n weakening:

  ArkLib GoodCoeffs det needs a square-row embedding Fin N ↪ ι
  with N = (e+1)+(e+deg) = 2e+deg+1. At this cell
      e+deg ≤ n and e+1 ≤ n both hold, but N = 262177 > n = 2^18,
  so the N×N determinant lemma does not instantiate (tallness
  deficit 33). RelUDR cannot be weakened to e+deg ≤ n.

The remaining edge is Johnson / BCIKS20 Appendix A: vanishing of
*maximal n×n minors* (MCA / candidate_of_base_mca), not the N×N det.
Puncture-to-tallness would need t ≥ 33 and 5^t blows the 2^-128 budget.

This file is a compile-checked arithmetic kernel only.
It does not bump ProtocolClaim / score.txt (still 5313).
-/

namespace ProximityPrize.SubmissionLower.HBaseMCA

/-- 5314 cell error parameter. Current promoted cell is 65541 (score 5313). -/
def e : Nat := 65552

/-- Degree 2^17. -/
def deg : Nat := 2 ^ 17

/-- Evaluation-domain size 2^18. -/
def n : Nat := 2 ^ 18

/-- Square size demanded by GoodCoeffs: (e+1) rows of the dual plus (e+deg). -/
def N : Nat := (e + 1) + (e + deg)

theorem deg_eq : deg = 131072 := by decide
theorem n_eq : n = 262144 := by decide
theorem N_eq : N = 262177 := by decide

/-- RelUDR-style row count still fits. -/
theorem e_add_deg_le_n : e + deg ≤ n := by decide

/-- Dual-side row count still fits. -/
theorem e_succ_le_n : e + 1 ≤ n := by decide

/-- Square-row embedding Fin N ↪ Fin n is blocked: N exceeds n. -/
theorem N_gt_n : n < N := by decide

/-- Tallness deficit: N - n = 33. -/
theorem tallness_deficit : N - n = 33 := by decide

/-- 2e − deg = 32 (off-by-one vs a 31-count that used 2e−d−1). -/
theorem two_e_sub_deg : 2 * e - deg = 32 := by decide

/-- N = n + 33, so any injective map Fin N → Fin n is impossible
    (cardinality). Recorded as the numeric obstruction; the MCA
    replacement is det ≡ 0 of every n×n minor, not this N×N det. -/
theorem N_eq_n_add_deficit : N = n + 33 := by decide

/-- Puncture count needed to restore tallness for the square embedding. -/
def puncture_t : Nat := 33

theorem puncture_restores_tallness : N ≤ n + puncture_t := by decide

/-- Raw 5^t vs 2^128 is *not* a blow-up: 2^76 < 5^33 < 2^77 < 2^128.
    Puncture-to-tallness costs ~77 bits of slack, not an overflow of the
    2^{-128} soundness *numerator*. Residual question is whether the
    current FRI/proximity slack is ≥ 77 bits (then t=33 puncture is live). -/
theorem two_pow_76_lt_five_pow_33 : 2 ^ 76 < 5 ^ 33 := by decide
theorem five_pow_33_lt_two_pow_77 : 5 ^ 33 < 2 ^ 77 := by decide
theorem five_pow_33_lt_two_pow_128 : 5 ^ 33 < 2 ^ 128 := by decide

end ProximityPrize.SubmissionLower.HBaseMCA
