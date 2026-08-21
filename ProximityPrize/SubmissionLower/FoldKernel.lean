/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize contributors
-/

/-!
# FoldKernel — IRS interleave-8 cannot split the 33-dim BW kernel

`GammaBaseOrder` already showed that the FRS unit `γ` of order `2^21` lives
in KoalaBear (`2^21 ∣ p-1`) and that the extra powers are fold-cosets
(`2^21 / 2^18 = 8 = IRSProfile.interleaving`), not extra `Index` points.

This file asks a different question: even if one could *fold* the length-`2^18`
word along those 8-cosets, can that cyclic-8 action cut the Berlekamp–Welch
kernel at cell `e = 65552` down to the rank-1 locator?

No. The BW column count at this cell is `Ncols = 2e + deg + 1 = 262177`, so
the rectangular excess is `Ncols - n = 33`. Then:

* `33 % 8 = 1`, so the kernel is **not** an 8-fold pullback of a smaller
  space (those would have dimension `0 (mod 8)`).
* Unique-decoding radius `eUnique = 65536` has excess `1`, also `≡ 1 (mod 8)`.
* The 16-past-unique slack adds exactly `32 = 2·16` columns, a multiple of
  the interleave, and therefore **preserves** the obstruction: fold-projection
  cannot isolate a 1-dimensional locator inside the 33-dimensional kernel.

This kills the remaining "use the IRS fold to manufacture `hbase`" route
without touching puncture budgets, N×N dets, ofBase/Gal descent, Johnson
radius, or `γ`-order lifting.
-/

namespace ProximityPrize.SubmissionLower.FoldKernel

def n : Nat := 2 ^ 18
def e : Nat := 65552
def eUnique : Nat := 65536
def deg : Nat := 2 ^ 17
def interleave : Nat := 8

/-- BW columns for `(Q₀, Q₁)` with `deg Q₁ ≤ e` and `deg Q₀ ≤ e + deg`. -/
def Ncols : Nat := 2 * e + deg + 1
def excess : Nat := Ncols - n

def NcolsUnique : Nat := 2 * eUnique + deg + 1
def excessUnique : Nat := NcolsUnique - n

def foldLen : Nat := n / interleave

theorem n_eq : n = 262144 := by native_decide
theorem Ncols_eq : Ncols = 262177 := by native_decide
theorem excess_eq : excess = 33 := by native_decide
theorem excessUnique_eq : excessUnique = 1 := by native_decide
theorem foldLen_eq : foldLen = 32768 := by native_decide

theorem past_unique : e - eUnique = 16 := by native_decide
theorem two_cols_per_error : excess - excessUnique = 2 * (e - eUnique) := by native_decide
theorem extra_dim_eq : excess - excessUnique = 32 := by native_decide

/-- Kernel dimension is `1 (mod interleave)`, not a fold pullback. -/
theorem excess_mod_eight : excess % interleave = 1 := by native_decide
theorem excessUnique_mod_eight : excessUnique % interleave = 1 := by native_decide
theorem extra_dim_divides_fold : (excess - excessUnique) % interleave = 0 := by native_decide
theorem kernel_not_fold_pullback : excess % interleave ≠ 0 := by native_decide
theorem not_mul_of_interleave : ¬ interleave ∣ excess := by native_decide

/-- Fold length is larger than the kernel, so the kernel cannot be
    "supported on one fold" in the dimension-count sense either. -/
theorem excess_lt_foldLen : excess < foldLen := by native_decide

/-- Rank-1 locator (`dim = 1`) is the same residue class as the 33-dim
    kernel; the fold cannot change the class. -/
theorem rank1_same_class : excess % interleave = excessUnique % interleave := by
  native_decide

end ProximityPrize.SubmissionLower.FoldKernel
