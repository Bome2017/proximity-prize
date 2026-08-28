/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_InseparableFinite

/-!
# The finite module supplied by the separable part

Tenth unit: the `D` that `integralClosure_finite_of_frobenius` consumes.

`D` is the set of elements of `L` that lie in the separable closure AND are
integral over `A`.  Stating it that way — two conditions on `y : L` rather
than a condition on `y : ↥(separableClosure F L)` — avoids needing an
`Algebra A ↥(separableClosure F L)` instance, and so avoids the
`IntermediateField` module diamond that blocks the obvious formulation.

* `sepIntegral` — the `A`-submodule of `L` spanned by that set;
* `pow_mem_sepIntegral` — `C ^ q ⊆ sepIntegral`, given the uniform
  inseparable exponent.  A power of an integral element is integral, and
  `x ^ q` lands in the separable part by hypothesis.

Finiteness of `sepIntegral` is what Mathlib's separable case supplies and is
tracked separately.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSepModule

set_option linter.unusedSectionVars false

variable {A F L : Type*} [CommRing A] [IsDomain A] [Field F] [Field L]
variable [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
variable [IsScalarTower A F L] [FiniteDimensional F L]

/-- The elements of `L` that are both separable over `F` and integral over
`A`.  Phrased entirely in `L`, so no `Algebra A ↥(separableClosure F L)`
instance is required. -/
def sepIntegralSet (A F L : Type*) [CommRing A] [Field F] [Field L]
    [Algebra A L] [Algebra F L] : Set L :=
  {y : L | y ∈ separableClosure F L ∧ IsIntegral A y}

/-- The `A`-submodule of `L` it spans. -/
def sepIntegral (A F L : Type*) [CommRing A] [Field F] [Field L]
    [Algebra A L] [Algebra F L] : Submodule A L :=
  Submodule.span A (sepIntegralSet A F L)

/-- **`C ^ q` lands in `sepIntegral`.**  A power of an integral element is
integral, and `x ^ q` lies in the separable part by the uniform exponent. -/
theorem pow_mem_sepIntegral (q : ℕ)
    (hexp : ∀ x : L, x ^ q ∈ separableClosure F L)
    (x : L) (hx : x ∈ integralClosure A L) :
    x ^ q ∈ sepIntegral A F L := by
  refine Submodule.subset_span ⟨hexp x, ?_⟩
  exact IsIntegral.pow hx q

end ProximityPrize.SubmissionLower.LocalMathlibSepModule

#print axioms ProximityPrize.SubmissionLower.LocalMathlibSepModule.pow_mem_sepIntegral
