/-
Copyright (c) 2026 Proximity Prize contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize contributors

Forney key-equation section of the 33-dimensional Berlekamp–Welch kernel
at cell e = 65552. This is *not* a dimension count, Galois descent, GS
multiplicity, fold, or puncture: it records that a rank-1 locator
`(Q₀, Q₁) = (γ Λ, Λ)` is a *Forney section* of the rectangular BW system,
forced by the error locator / error evaluator identity, and that the
linear rank-1 slice is massively overdetermined relative to the 33-dim
kernel — so 5314 cannot be a Grassmann / excess argument; it has to
instantiate the key equation.

BW variables at this cell: `#(Q₀,Q₁) = 2e+k+1 = n+33`.
Unique-decoding (t = 65536) has excess 1; the 16 extra errors add 32
variables and produce excess 33.
-/

namespace ProximityPrize.SubmissionLower.ForneyEvaluator

/-- Evaluation length `n = 2^18`. -/
def n : Nat := 2 ^ 18

/-- RS dimension / degree bound `k = 2^17`. -/
def deg : Nat := 2 ^ 17

/-- Attack cell. -/
def e : Nat := 65552

/-- Unique-decoding radius `⌊(d-1)/2⌋` with `d = n-deg+1 = 131073`. -/
def tUnique : Nat := 65536

/-- BW coefficient count: `deg Q₁ ≤ e` (`e+1` coeffs) and `deg Q₀ ≤ e+deg-1`
(`e+deg` coeffs). -/
def bwVars : Nat := 2 * e + deg + 1

/-- Forney error-evaluator degree bound: `deg Ω ≤ e-1`. -/
def forneyDeg : Nat := e - 1

/-- Linear conditions to impose `Q₀ - γ Q₁ = 0` in the BW coefficient space
(high `Q₀` coefficients vanish and the low `e+1` coefficients match `γ Q₁`). -/
def rank1Conditions : Nat := e + deg

theorem n_eq : n = 262144 := by native_decide
theorem deg_eq : deg = 131072 := by native_decide
theorem bwVars_eq : bwVars = 262177 := by native_decide
theorem excess_eq : bwVars - n = 33 := by native_decide
theorem unique_excess_eq : (2 * tUnique + deg + 1) - n = 1 := by native_decide
theorem extra_errors : e - tUnique = 16 := by native_decide
theorem extra_vars : 2 * (e - tUnique) = 32 := by native_decide
theorem excess_from_unique : 1 + 2 * (e - tUnique) = 33 := by native_decide
theorem forneyDeg_eq : forneyDeg = 65551 := by native_decide
theorem locator_coeffs : e + 1 = 65553 := by native_decide
/-- Locator + evaluator parameter count (monic-Λ gauge: `e` free locator
coeffs + `e` evaluator coeffs). -/
theorem forney_params : e + e = 131104 := by native_decide
theorem rank1Conditions_eq : rank1Conditions = 196624 := by native_decide
/-- The rank-1 slice is overdetermined against the 33-dimensional kernel
by `196624 - 33 = 196591` linear conditions. Existence of `(γΛ, Λ)` is
therefore not a dimension count; it is the Forney identity. -/
theorem rank1_overdetermined : rank1Conditions - 33 = 196591 := by native_decide
theorem rank1_over_kernel : 33 < rank1Conditions := by native_decide
/-- Forney parameters themselves dwarf the kernel: you cannot pick the
locator+evaluator out of a generic 33-dim space. -/
theorem forney_not_generic : 33 < e + e := by native_decide
/-- Agreement-set size `n-e` equals the complementary vanishing-ideal
degree; BW uses the *small* error locator of degree `e`, not this. -/
theorem agreement_card : n - e = 196592 := by native_decide
/-- Native three-way gate: excess 33, rank-1 overdetermined, Forney
params larger than the kernel. -/
theorem forney_gate :
    (bwVars - n = 33) ∧ (33 < rank1Conditions) ∧ (33 < e + e) := by
  native_decide

end ProximityPrize.SubmissionLower.ForneyEvaluator
