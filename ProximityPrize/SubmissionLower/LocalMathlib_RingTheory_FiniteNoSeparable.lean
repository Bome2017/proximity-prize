/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SepModuleFinite

/-!
# Finiteness of the integral closure, unconditionally

The capstone.  Mathlib's `IsIntegralClosure.finite` carries
`[Algebra.IsSeparable F L]`, and demanding it is exactly what forces the
mixed-bidegree gate `yCap * seedTotalCap < 4064` through
`ContactProjectionParameters.all_projection_caps_below_characteristic`.

Here that hypothesis is gone.  What replaces it is data that the base ring
supplies for free over a perfect field: a subring `A₀ ⊆ A` with a ring
isomorphism `σ : A ≃+* A₀` realising the `q`-power map, `A` finite over the
Noetherian `A₀`, and a uniform exponent `q` sending all of `L` into the
separable closure.

* `integralClosure_finite_of_frobeniusBase` — `Module.Finite A
  (integralClosure A L)` with no separability hypothesis on `L / F`.

At `A = K[X]` over a perfect `K` every input is already proved:
`σ = frobEquiv`, `A₀ = expandRange`, Noetherian and finite by
`expandRange_isNoetherianRing` and `finite_over_expand`, and the exponent by
`exists_uniform_exponent` applied to `L / separableClosure F L`.

Combined with `isDedekindDomain_of_moduleFinite` this discharges all three
uses of separability in `FixedCurveNormSum`, which is the only place the
whole contact chain needs it.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibFiniteNoSeparable

open LocalMathlibSepModule LocalMathlibSepModuleFinite LocalMathlibInseparableFinite

set_option linter.unusedSectionVars false

variable {A F L : Type*} [CommRing A] [IsDomain A] [Field F] [Field L]
variable [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
variable [IsScalarTower A F L] [FiniteDimensional F L]
variable [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **The integral closure is finite, with no separability hypothesis.**

The separability of `L / F` that Mathlib requires is replaced by the
Frobenius structure on the base together with a uniform inseparable
exponent — both of which are available over a perfect field. -/
theorem integralClosure_finite_of_frobeniusBase
    (p e : ℕ) [ExpChar L p]
    (A₀ : Subring A) (σ : A ≃+* A₀) (hσ : ∀ a : A, ((σ a : A)) = a ^ p ^ e)
    (hA₀ : IsNoetherianRing A₀) (hfin : Module.Finite A₀ A)
    (hexp : ∀ x : L, x ^ p ^ e ∈ separableClosure F L) :
    Module.Finite A (integralClosure A L) :=
  integralClosure_finite_of_frobenius p e A₀ σ hσ hA₀ hfin
    (sepIntegral A F L) sepIntegral_finite
    (fun x hx => pow_mem_sepIntegral (p ^ e) hexp x hx)

end ProximityPrize.SubmissionLower.LocalMathlibFiniteNoSeparable

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibFiniteNoSeparable.integralClosure_finite_of_frobeniusBase
