/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_PolynomialFinite

/-!
# Explicit `q`-power decompositions

Towards the infinity chart.  `InfinityBase K` is a valuation subring, not a
polynomial ring, so `finite_over_expand` does not apply to it.  The
replacement argument is ultrametric, and it needs an EXPLICIT decomposition
`f = ∑ (cᵢ) ^ q * u ^ i` rather than mere membership in a span.

* `exists_polynomial_pow_decomposition` — over a perfect `K`, every
  polynomial is `∑_{i < q} hᵢ ^ q * X ^ i`.  This is
  `span_range_X_pow_eq_top` made explicit, with the coefficients turned into
  `q`-th powers by `exists_pow_eq_of_mem_expandRange`.

The valuations of the terms `hᵢ ^ q * u ^ i` are pairwise distinct because
they are distinct mod `q`, which is what lets `Valuation.map_sum_eq_of_lt`
identify the valuation of the sum with the maximum — and hence force every
coefficient into the valuation ring.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibPowDecomposition

open Polynomial LocalMathlibExpandFinite LocalMathlibExpandFrobenius

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- **Every polynomial is an explicit `q`-power combination of `1, X, …,
X^(q-1)`.** -/
theorem exists_polynomial_pow_decomposition (f : Polynomial K) :
    ∃ h : Fin (p ^ e) → Polynomial K,
      f = ∑ i : Fin (p ^ e), (h i) ^ p ^ e * (Polynomial.X : Polynomial K) ^ (i : ℕ) := by
  classical
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  have hspan := span_range_X_pow_eq_top K (p ^ e) hq
  have hmem : f ∈ Submodule.span (expandRange K (p ^ e))
      (Set.range fun i : Fin (p ^ e) => (Polynomial.X : Polynomial K) ^ (i : ℕ)) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hmem
  -- each coefficient of the combination is a `q`-th power, `K` being perfect
  choose g hg using fun i : Fin (p ^ e) =>
    exists_pow_eq_of_mem_expandRange K p e (c i : Polynomial K) (c i).2
  refine ⟨g, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  rfl

/-- **Every rational function is an explicit `q`-power combination of
`1, X, …, X^(q-1)`.**  Write `f = P / Q`, decompose `P * Q^(q-1)`, and divide
through by `Q^q`. -/
theorem exists_ratfunc_pow_decomposition (f : RatFunc K) :
    ∃ c : Fin (p ^ e) → RatFunc K,
      f = ∑ i : Fin (p ^ e), (c i) ^ p ^ e * (RatFunc.X : RatFunc K) ^ (i : ℕ) := by
  classical
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  obtain ⟨h, hh⟩ :=
    exists_polynomial_pow_decomposition K p e (f.num * f.denom ^ (p ^ e - 1))
  set Φ := algebraMap (Polynomial K) (RatFunc K) with hΦ
  have hden : Φ f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hnd : Φ f.num / Φ f.denom = f := RatFunc.num_div_denom f
  refine ⟨fun i => Φ (h i) / Φ f.denom, ?_⟩
  -- push the ring map through the decomposition
  have hmap : Φ f.num * Φ f.denom ^ (p ^ e - 1)
      = ∑ i : Fin (p ^ e), Φ (h i) ^ p ^ e * (RatFunc.X : RatFunc K) ^ (i : ℕ) := by
    have := congrArg Φ hh
    rw [map_mul, map_pow, map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, map_pow, map_pow]
    congr 1
  -- exponent bookkeeping, kept away from the indexed sum
  have hQpow : Φ f.denom ^ (p ^ e - 1) * Φ f.denom = Φ f.denom ^ (p ^ e) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfd : Φ f.num = f * Φ f.denom := (div_eq_iff hden).mp hnd
  have hkey : f * Φ f.denom ^ (p ^ e) = Φ f.num * Φ f.denom ^ (p ^ e - 1) := by
    rw [hfd, ← hQpow]; ring
  -- pull the common denominator out of the sum
  have hRHS : (∑ i : Fin (p ^ e), (Φ (h i) / Φ f.denom) ^ p ^ e *
        (RatFunc.X : RatFunc K) ^ (i : ℕ))
      = (∑ i : Fin (p ^ e), Φ (h i) ^ p ^ e * (RatFunc.X : RatFunc K) ^ (i : ℕ))
        / Φ f.denom ^ p ^ e := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
    ring
  rw [hRHS, ← hmap, ← hkey, mul_div_assoc, div_self (pow_ne_zero _ hden), mul_one]

end ProximityPrize.SubmissionLower.LocalMathlibPowDecomposition

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPowDecomposition.exists_polynomial_pow_decomposition
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPowDecomposition.exists_ratfunc_pow_decomposition
