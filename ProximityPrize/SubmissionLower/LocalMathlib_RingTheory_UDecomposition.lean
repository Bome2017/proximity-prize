/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_PowDecomposition

/-!
# Decomposition in the `u = X⁻¹` basis

The infinity chart needs the spanning set to lie INSIDE the valuation ring,
and `X ^ i` does not — it has a pole at infinity.  The right basis there is
`u = X⁻¹`.

Converting is a reindexing: `X ^ q * u ^ k = X ^ (q - k)` for `k ≤ q`, so
the `i`-th term `cᵢ ^ q * X ^ i` becomes `(cᵢ * X) ^ q * u ^ (q - i)`.  On
`i ∈ [1, q-1]` the map `i ↦ q - i` is the reflection
`Finset.sum_range_reflect`, and the `i = 0` term stays put.

* `exists_ratfunc_pow_decomposition_range` — the `Fin` sum as a
  `Finset.range` sum, so that `q - i` is expressible;
* `exists_u_decomposition` — every `f` is `∑_{j < q} (d j) ^ q * u ^ j`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibUDecomposition

open Polynomial LocalMathlibPowDecomposition

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

theorem X_ne_zero : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero

/-- `X ^ q * u ^ k = X ^ (q - k)` for `k ≤ q`. -/
theorem X_pow_mul_inv_pow (q k : ℕ) (hk : k ≤ q) :
    (RatFunc.X : RatFunc K) ^ q * ((RatFunc.X : RatFunc K)⁻¹) ^ k
      = (RatFunc.X : RatFunc K) ^ (q - k) := by
  rw [inv_pow]
  exact (pow_sub₀ _ (X_ne_zero K) hk).symm

/-- The decomposition indexed by `Finset.range` rather than `Fin`. -/
theorem exists_ratfunc_pow_decomposition_range (f : RatFunc K) :
    ∃ c : ℕ → RatFunc K,
      f = ∑ i ∈ Finset.range (p ^ e), (c i) ^ p ^ e * (RatFunc.X : RatFunc K) ^ i := by
  classical
  obtain ⟨c, hc⟩ := exists_ratfunc_pow_decomposition K p e f
  refine ⟨fun i => if h : i < p ^ e then c ⟨i, h⟩ else 0, ?_⟩
  rw [hc, ← Fin.sum_univ_eq_sum_range
    (fun i => (if h : i < p ^ e then c ⟨i, h⟩ else 0) ^ p ^ e *
      (RatFunc.X : RatFunc K) ^ i) (p ^ e)]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

/-- **Every rational function is a `q`-power combination of `1, u, …,
u^(q-1)`.** -/
theorem exists_u_decomposition (f : RatFunc K) :
    ∃ d : ℕ → RatFunc K,
      f = ∑ j ∈ Finset.range (p ^ e),
        (d j) ^ p ^ e * ((RatFunc.X : RatFunc K)⁻¹) ^ j := by
  classical
  obtain ⟨c, hc⟩ := exists_ratfunc_pow_decomposition_range K p e f
  obtain ⟨m, hm⟩ : ∃ m, p ^ e = m + 1 := ⟨p ^ e - 1, by have := pow_pos hp.out.pos e; omega⟩
  refine ⟨fun j => if j = 0 then c 0 else c (p ^ e - j) * (RatFunc.X : RatFunc K), ?_⟩
  rw [hc, hm, Finset.sum_range_succ', Finset.sum_range_succ']
  congr 1
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  have hidx : m - 1 - j + 1 = m - j := by omega
  have hif : (if j + 1 = 0 then c 0 else c (m + 1 - (j + 1)) * (RatFunc.X : RatFunc K))
      = c (m - j) * (RatFunc.X : RatFunc K) := by
    rw [if_neg (Nat.succ_ne_zero j)]
    congr 2
    omega
  have hexp : m + 1 - (j + 1) = m - j := by omega
  dsimp only
  rw [hidx, hif, mul_pow, mul_assoc,
    X_pow_mul_inv_pow K (m + 1) (j + 1) (by omega), hexp]

end ProximityPrize.SubmissionLower.LocalMathlibUDecomposition

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibUDecomposition.exists_u_decomposition
