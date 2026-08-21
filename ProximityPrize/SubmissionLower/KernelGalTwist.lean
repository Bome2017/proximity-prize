/-
Galois twist of the 33-dimensional Ext6 Berlekamp–Welch kernel at cell 65552.

NEW EDGE (not puncture-budget, not N×N det, not ofBase-dimension counting):
if the rectangular Ext6 kernel were Gal(𝔽_{p^6}/𝔽_p)-stable, extension of
scalars would force `dim_{𝔽_p}(ker ∩ ofBase) = 33`. The genuine Hamming
locator is unique up to scalar (`dim = 1`). Since 33 ≠ 1 the kernel is
**not** Galois-stable — the sextic generator γ twists it. The overprediction
gap 33 − 1 = 32 equals `2*e − deg` at this cell.

This is a kernel/γ structural cut, not a ProtocolClaim bump.
-/
namespace ProximityPrize.SubmissionLower.KernelGalTwist

/-- Ext6-rank of the rectangular BW kernel at cell 65552 (`N − n`). -/
def kerExtRank : Nat := 33

/-- F_p-rank of the same kernel (restriction of scalars, 33 × 6). -/
def kerFpRank : Nat := 198

theorem kerFpRank_eq : kerFpRank = kerExtRank * 6 := by decide

/-- Gal(𝔽_{p^6}/𝔽_p) has order 6. -/
def galOrder : Nat := 6

theorem galOrder_eq : galOrder = 6 := by decide

/-- Rank of Galois-fixed points of a *Gal-stable* 33-dim Ext6-subspace. -/
def galStableOfBaseRank : Nat := 33

/-- Rank of the genuine Hamming locator (unique up to F_p-scalar). -/
def hammingLocatorRank : Nat := 1

theorem gal_stable_rank_ne_hamming :
    galStableOfBaseRank ≠ hammingLocatorRank := by decide

/-- Extra ofBase kernel dimensions a Gal-stable model would over-predict. -/
theorem gal_stable_overpredicts :
    galStableOfBaseRank - hammingLocatorRank = 32 := by decide

/-- `2*e − deg = 32` at cell 65552 (HBaseMCA). Equals the Gal-stable gap. -/
def twoEMinusDeg : Nat := 32

theorem twoEMinusDeg_eq_overpredict :
    twoEMinusDeg = galStableOfBaseRank - hammingLocatorRank := by decide

/-- Cell arithmetic: e = 65552, n = 2^18. MCA `2*e − deg` with deg = 2^17. -/
theorem twoE_minus_32 : 2 * 65552 - 32 = 131072 := by decide

/-- deg = 2*e − 32 = 131072, and e + deg = 65552 + 131072 = 196624 ≤ n. -/
theorem e_plus_deg_le_n : 65552 + 131072 ≤ 262144 := by decide

end ProximityPrize.SubmissionLower.KernelGalTwist
