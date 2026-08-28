/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_FiniteNoSeparable

/-!
# `K[X]`-finiteness of the integral closure over a perfect `K`

The capstone `integralClosure_finite_of_frobeniusBase`, instantiated at the
base `A = K[X]`.  Every input is already proved:

* `σ = frobEquiv`, `A₀ = expandRange` — the `q`-power isomorphism;
* `expandRange_isNoetherianRing`, `finite_over_expand`;
* the uniform inseparable exponent, applied to `L / separableClosure`.

This is the form `FixedCurveNormSum.finiteNormalization_finite` needs, with
`Algebra.IsSeparable (RatFunc K) L` deleted.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibPolynomialFinite

open Polynomial LocalMathlibExpandFinite LocalMathlibExpandFrobenius
open LocalMathlibExpandEquiv LocalMathlibUniformInseparableExponent
open LocalMathlibFiniteNoSeparable

set_option linter.unusedSectionVars false

variable (K L : Type*) [Field K] [Field L]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L]

/-- **`K[X]`-finiteness with no separability hypothesis.** -/
theorem polynomial_integralClosure_finite (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectRing K p] :
    Module.Finite (Polynomial K) (integralClosure (Polynomial K) L) := by
  classical
  haveI : CharP (RatFunc K) p :=
    charP_of_injective_algebraMap
      (IsFractionRing.injective (Polynomial K) (RatFunc K)) p
  haveI : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (RatFunc K) L).injective p
  haveI : ExpChar L p := ExpChar.prime (Fact.out)
  set M := separableClosure (RatFunc K) L with hM
  haveI : CharP M p :=
    charP_of_injective_algebraMap (algebraMap (RatFunc K) M).injective p
  haveI : ExpChar M p := ExpChar.prime (Fact.out)
  haveI : IsPurelyInseparable M L := separableClosure.isPurelyInseparable (RatFunc K) L
  haveI : FiniteDimensional M L := FiniteDimensional.right (RatFunc K) M L
  obtain ⟨e, he⟩ := exists_uniform_exponent M L p
  refine integralClosure_finite_of_frobeniusBase (F := RatFunc K) p e
    (expandRange K (p ^ e)) (frobEquiv K p e) (fun a => rfl)
    (expandRange_isNoetherianRing K p e)
    (finite_over_expand K (p ^ e) (pow_pos (Fact.out : p.Prime).pos e))
    (fun x => ?_)
  obtain ⟨y, hy⟩ := he x
  rw [← hy]
  exact y.2

end ProximityPrize.SubmissionLower.LocalMathlibPolynomialFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPolynomialFinite.polynomial_integralClosure_finite
