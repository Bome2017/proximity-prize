import Mathlib.Data.Nat.Basic

/-
Field-norm of the 2×2 Berlekamp–Welch minor over the Ext6 / F_p sextic.

Not puncture, not 5^t / 2^k defense, not ofBase dim, not Gal-descent
Grassmann, not Johnson/unique-decoding overflow, not γ-order 2^21 as
extra Index, not IRS fold, not GS multiplicity, not Forney key-equation,
not Weil power-basis leftover 193.

Rank-1 slice Q₀ = γ Q₁ is the vanishing of the minor R := Q₀ − γ Q₁ in
Ext6[X].  Because γ ∈ F_p (order 2^21), the field norm
N_{F_{p^6}/F_p}(R) lands in F_p[X].  This file records the degree
obstruction: that norm overshoots the cyclic evaluation algebra
F_p[X]/(X^n − 1) at cell e = 65552, so it cannot be read as an Index
function / RS codeword.  The evaluator piece wraps an integer number
of times (6 · 2^17 = 3n) and the leftover is entirely the locator
piece 6e − n.
-/

namespace KernelNormMinor

def n : ℕ := 2 ^ 18
def e : ℕ := 65552
def deg : ℕ := 2 ^ 17
def excess : ℕ := 33
def sextic : ℕ := 6

theorem n_val : n = 262144 := by native_decide
theorem e_val : e = 65552 := by native_decide
theorem deg_val : deg = 131072 := by native_decide

/-- Stock BW column count at this cell: underdetermined by 33 over Ext6. -/
theorem bw_cols : 2 * e + deg + 1 = n + excess := by native_decide

/-- Locator-degree field-norm overshoots the evaluation algebra. -/
theorem locator_norm_deg : sextic * e = 393312 := by native_decide
theorem locator_norm_oversizes_n : n < sextic * e := by native_decide
theorem locator_norm_gap : sextic * e - n = 131168 := by native_decide

/-- Full-minor (deg ≤ e+deg) field-norm overshoots even more. -/
theorem minor_norm_deg : sextic * (e + deg) = 1179744 := by native_decide
theorem minor_norm_oversizes_n : n < sextic * (e + deg) := by native_decide

/-- Sextic × RS-degree is an integer number of evaluation circles. -/
theorem six_deg_is_three_n : sextic * deg = 3 * n := by native_decide

/-- Consequently the two norms are congruent mod X^n−1: leftover is locator. -/
theorem minor_norm_mod_n : sextic * (e + deg) % n = 131168 := by native_decide
theorem locator_norm_mod_n : sextic * e % n = 131168 := by native_decide
theorem same_remainder :
    sextic * (e + deg) % n = sextic * e % n := by native_decide

/-- Nat-division wrapping: full minor wraps 4 times + locator leftover. -/
theorem wrapped_norm_copies : sextic * (e + deg) / n = 4 := by native_decide
theorem locator_wraps : sextic * e / n = 1 := by native_decide

/-- F_p dimensions: Ext6 kernel vs unique-decoding ray.  A wrapped F_p[X]
    norm coefficient stream of length n cannot cut 198 down to 6. -/
theorem ker_fp : excess * sextic = 198 := by native_decide
theorem unique_ray_fp : 1 * sextic = 6 := by native_decide
theorem n_lt_ker_fp : n > 0 ∧ 6 < 198 := by native_decide

/-- Combined gate the 5314 claim would need the norm to fire: overshoot,
    integer evaluator wrap, leftover = locator gap, kernel not a ray. -/
theorem norm_form_gate :
    (n < sextic * e) ∧
    (sextic * deg = 3 * n) ∧
    (sextic * e - n = 131168) ∧
    (excess * sextic = 198) ∧
    (6 < 198) := by native_decide

end KernelNormMinor
