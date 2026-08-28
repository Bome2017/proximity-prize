/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_InfinityFinite

/-!
# Finiteness over a perfect base, with the characteristic eliminated

`polynomial_integralClosure_finite` and `infinity_integralClosure_finite`
take the characteristic `p` as an explicit parameter.  Threading `p` through
the fourteen downstream modules that currently carry
`[Algebra.IsSeparable (RatFunc K) L]` would be a large and invasive change.

It is unnecessary: the conclusions do not mention `p`, so it can be
discharged internally by casing on the characteristic.

* characteristic `0` — then `RatFunc K` is perfect, every algebraic
  extension of it is separable, and Mathlib's own theorem applies;
* characteristic `p` prime — then `PerfectField K` gives `PerfectRing K p`
  and the Frobenius descent applies.

So the downstream refactor is just `[Algebra.IsSeparable (RatFunc K) L] ↦
[PerfectField K]`, and in the application `K` is algebraically closed, which
already gives `PerfectField K`.

* `polynomial_finite_of_perfect`, `infinity_finite_of_perfect`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibPerfectBaseFinite

open LocalMathlibPolynomialFinite LocalMathlibInfinityFinite LocalMathlibInfinityPowFinite

set_option linter.unusedSectionVars false

variable (K L : Type*) [Field K] [PerfectField K] [Field L]

/-- In characteristic zero the extension is automatically separable. -/
theorem isSeparable_of_charZero [Algebra (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] (h : ringChar K = 0) :
    Algebra.IsSeparable (RatFunc K) L := by
  haveI : CharP K 0 := h ▸ ringChar.charP K
  haveI : CharZero K := CharP.charP_to_charZero K
  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  infer_instance

/-- **Polynomial chart, characteristic eliminated.** -/
theorem polynomial_finite_of_perfect
    [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
    [IsScalarTower (Polynomial K) (RatFunc K) L] [FiniteDimensional (RatFunc K) L] :
    Module.Finite (Polynomial K) (integralClosure (Polynomial K) L) := by
  classical
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · haveI : Fact (ringChar K).Prime := ⟨hp⟩
    haveI : CharP K (ringChar K) := ringChar.charP K
    haveI : ExpChar K (ringChar K) := ExpChar.prime hp
    haveI : PerfectRing K (ringChar K) := inferInstance
    exact polynomial_integralClosure_finite K L (ringChar K)
  · haveI := isSeparable_of_charZero K L h0
    exact IsIntegralClosure.finite (Polynomial K) (RatFunc K) L _

/-- **Infinity chart, characteristic eliminated.** -/
theorem infinity_finite_of_perfect
    [Algebra (IR K) L] [Algebra (RatFunc K) L]
    [IsScalarTower (IR K) (RatFunc K) L] [FiniteDimensional (RatFunc K) L] :
    Module.Finite (IR K) (integralClosure (IR K) L) := by
  classical
  haveI : IsFractionRing (IR K) (RatFunc K) :=
    InfinityValuationRing.infinityRing_isFractionRing K
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · haveI : Fact (ringChar K).Prime := ⟨hp⟩
    haveI : CharP K (ringChar K) := ringChar.charP K
    haveI : ExpChar K (ringChar K) := ExpChar.prime hp
    haveI : PerfectRing K (ringChar K) := inferInstance
    exact infinity_integralClosure_finite K (ringChar K) L
  · haveI := isSeparable_of_charZero K L h0
    exact IsIntegralClosure.finite (IR K) (RatFunc K) L _

end ProximityPrize.SubmissionLower.LocalMathlibPerfectBaseFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPerfectBaseFinite.polynomial_finite_of_perfect
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPerfectBaseFinite.infinity_finite_of_perfect
