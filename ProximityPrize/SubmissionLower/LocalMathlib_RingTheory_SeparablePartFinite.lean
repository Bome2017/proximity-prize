/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_FrobeniusDescent

/-!
# The integral closure in the separable part is finite

Sixth unit: the first input to `finite_of_frobenius_descent`.

`M = separableClosure F L` is separable over `F` by construction, so
Mathlib's separable case applies verbatim at `M` even though it does not
apply at `L`.  That gives the finite module `D` the descent needs.

* `separablePart_finite` — `Module.Finite A (integralClosure A M)` where
  `M` is the separable closure of `F = Frac A` inside `L`.

Everything here is Mathlib's separable machinery, instantiated at `M`; the
point is only that `M` is where it is legitimate to use it.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSeparablePartFinite

open IntermediateField

set_option linter.unusedSectionVars false

variable (A F L : Type*) [CommRing A] [IsDomain A] [Field F] [Field L]
variable [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
variable [IsScalarTower A F L] [FiniteDimensional F L]
variable [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **The integral closure in a separable intermediate field is finite.**
Stated for a general intermediate field `M` with its algebra instances as
hypotheses, so that no `Algebra A ↥M` instance is declared globally — a
generic one would fire at `A := F` and shadow `IntermediateField.algebra'`.

Applied with `M = separableClosure F L`, this is the first input to
`finite_of_frobenius_descent`: Mathlib's separable theorem is legitimate at
`M` even though it is not at `L`. -/
theorem finite_integralClosure_of_separable
    (M : IntermediateField F L) [Algebra A M] [IsScalarTower A F M]
    [Algebra.IsSeparable F M] :
    Module.Finite A (integralClosure A M) := by
  haveI : FiniteDimensional F M := FiniteDimensional.left F M L
  exact IsIntegralClosure.finite A F M (integralClosure A M)

/-- The separable closure is separable, so the hypothesis above is available
at `M = separableClosure F L`. -/
theorem isSeparable_separableClosure :
    Algebra.IsSeparable F (separableClosure F L) :=
  separableClosure.isSeparable F L

end ProximityPrize.SubmissionLower.LocalMathlibSeparablePartFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSeparablePartFinite.finite_integralClosure_of_separable
