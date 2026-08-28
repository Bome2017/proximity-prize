/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_UltrametricCoeff
import ProximityPrize.SubmissionLower.InfinityValuationRing

/-!
# The infinity valuation ring is finite over its `q`-th powers

The analogue of `finite_over_expand` for the infinity chart.  `InfinityBase K`
is a valuation subring, not a polynomial ring, so the polynomial argument
does not apply; the replacement is ultrametric.

Every `a` in the ring decomposes as `∑_{j < q} (d j) ^ q * u ^ j` over the
whole field (`exists_u_decomposition`), and the ultrametric step
(`coeff_mem_of_sum_mem`) puts every `d j` back inside the ring.  Since
`u = X⁻¹` also lies in the ring, `1, u, …, u^(q-1)` is a spanning set over
the subring of `q`-th powers.

* `frobRange` — the subring of `q`-th powers;
* `finite_over_frobRange` — `Module.Finite (frobRange) (InfinityRing K)`.

That is the last input the capstone needs for the infinity chart.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibInfinityPowFinite

open LocalMathlibUDecomposition LocalMathlibUltrametricCoeff InfinityValuationRing

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The infinity valuation ring. -/
noncomputable abbrev IR := InfinityValuationRing.InfinityRing K

instance charP_ratfunc : CharP (RatFunc K) p :=
  charP_of_injective_algebraMap (IsFractionRing.injective (Polynomial K) (RatFunc K)) p

theorem charP_IR : CharP (IR K) p where
  cast_eq_zero_iff n := by
    haveI := charP_ratfunc K p
    rw [← CharP.cast_eq_zero_iff (RatFunc K) p n]
    constructor
    · intro h
      have h2 := congrArg (fun z : IR K => (z : RatFunc K)) h
      simpa using h2
    · intro h
      apply Subtype.ext
      simpa using h

theorem expChar_IR : ExpChar (IR K) p :=
  letI := charP_IR K p
  ExpChar.prime hp.out

attribute [local instance] charP_IR expChar_IR

/-- The subring of `q`-th powers. -/
noncomputable def frobRange : Subring (IR K) :=
  (iterateFrobenius (IR K) p e).range

/-- The uniformizer `u = X⁻¹`, as an element of the ring. -/
noncomputable def uIR : IR K := InfinityValuationRing.infinityUniformizer K

theorem uIR_coe : ((uIR K : IR K) : RatFunc K) = (RatFunc.X : RatFunc K)⁻¹ := by
  show ((InfinityValuationRing.infinityUniformizer K : IR K) : RatFunc K) = _
  simp [InfinityValuationRing.infinityUniformizer]

noncomputable instance : Algebra (frobRange K p e) (IR K) :=
  (frobRange K p e).subtype.toAlgebra

/-- **The infinity ring is finite over its `q`-th powers.** -/
theorem finite_over_frobRange : Module.Finite (frobRange K p e) (IR K) := by
  classical
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  refine ⟨⟨(Finset.range (p ^ e)).image (fun j => (uIR K) ^ j), ?_⟩⟩
  rw [eq_top_iff]
  rintro a -
  -- decompose the underlying rational function
  obtain ⟨d, hd⟩ := exists_u_decomposition K p e ((a : IR K) : RatFunc K)
  -- the coefficients land back in the ring
  have hcoef : ∀ j, j < p ^ e → RatFunc.inftyValuation K (d j) ≤ 1 := by
    intro j hj
    refine coeff_mem_of_sum_mem K (p ^ e) hq d ?_ j hj
    rw [← hd]
    exact a.2
  -- lift the decomposition into the ring
  set c : ℕ → IR K := fun j => if h : j < p ^ e then ⟨d j, hcoef j h⟩ else 0 with hc
  have hlift : a = ∑ j ∈ Finset.range (p ^ e), (c j) ^ p ^ e * (uIR K) ^ j := by
    apply Subtype.ext
    push_cast
    rw [hd]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < p ^ e := Finset.mem_range.mp hj
    rw [uIR_coe]
    congr 1
    simp [hc, hj']
  rw [hlift]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hj' : j < p ^ e := Finset.mem_range.mp hj
  have hcoeff : (c j) ^ p ^ e ∈ frobRange K p e := ⟨c j, rfl⟩
  have hbasis : (uIR K) ^ j ∈
      ((Finset.range (p ^ e)).image (fun j => (uIR K) ^ j) : Finset (IR K)) :=
    Finset.mem_image.mpr ⟨j, hj, rfl⟩
  exact Submodule.smul_mem _ (⟨_, hcoeff⟩ : frobRange K p e)
    (Submodule.subset_span (Finset.mem_coe.mpr hbasis))

end ProximityPrize.SubmissionLower.LocalMathlibInfinityPowFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInfinityPowFinite.finite_over_frobRange
