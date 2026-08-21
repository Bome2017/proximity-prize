/-
Unique-decoding overflow vs Johnson interior at cell 65552.

Not puncture-budget, not N×N GoodCoeffs det, not kernel existence, not
ofBase-dimension, not Galois-descent Grassmann. The RS unique-decoding
radius is 16 short of e, while e still sits strictly inside the Johnson
radius. The 33-dim BW kernel therefore cannot be reduced by unique
decoding / Berlekamp–Massey; 5314 is a Johnson/MCA (BCIKS20 App A)
statement. Extra-puncture budget 7 cannot walk e back to unique decoding.
-/

namespace UniqueJohnsonCut

def e : Nat := 65552
def deg : Nat := 131072
def n : Nat := 262144
def excess : Nat := 33
def extraPunctureBudget : Nat := 7

/-- RS[n, k=deg] designed distance n − k + 1. -/
def d : Nat := n - deg + 1

theorem d_val : d = 131073 := by native_decide

/-- Unique-decoding radius ⌊(d−1)/2⌋. -/
def tUnique : Nat := (d - 1) / 2

theorem tUnique_val : tUnique = 65536 := by native_decide

/-- Cell 65552 sits exactly 16 errors past unique decoding. -/
theorem unique_overflow : e - tUnique = 16 := by native_decide

theorem e_gt_unique : tUnique < e := by native_decide

/-- Johnson interior test: (n−e)² > n(n−d) ⇒ e < n − √(n(n−d)). -/
def nMinusE : Nat := n - e
def nMinusD : Nat := n - d

theorem nMinusE_val : nMinusE = 196592 := by native_decide
theorem nMinusD_val : nMinusD = 131071 := by native_decide

theorem johnson_interior :
    nMinusE * nMinusE > n * nMinusD := by native_decide

theorem johnson_gap :
    nMinusE * nMinusE - n * nMinusD = 4288938240 := by native_decide

/-- Extra unique-decoding errors (16) exceed extra-puncture FRI budget (7). -/
theorem unique_overflow_gt_puncture_budget :
    extraPunctureBudget < e - tUnique := by native_decide

/-- Berlekamp–Massey uniqueness window 2(e+1) vs rectangular excess 33. -/
theorem bm_window_vs_excess : excess < 2 * (e + 1) := by native_decide

/-- Even the unique-decoding locator length e+1 dwarfs the 33-dim kernel. -/
theorem locator_len_gt_excess : excess < e + 1 := by native_decide

/-- Rate-½ Johnson radius is larger than e, unique radius is not.
    5314 cannot be unique decoding on the 33-dim kernel. -/
theorem e_between_unique_and_johnson :
    tUnique < e ∧ nMinusE * nMinusE > n * nMinusD :=
  ⟨e_gt_unique, johnson_interior⟩

end UniqueJohnsonCut
