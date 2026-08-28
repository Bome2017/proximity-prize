/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_PowImage

/-!
# The integral closure is finite with no separability hypothesis

Ninth unit: the assembly.

This is the theorem the whole chain exists to prove.  Mathlib's
`IsIntegralClosure.finite` needs `Algebra.IsSeparable F L`; demanding it is
what forces `ContactProjectionParameters
.all_projection_caps_below_characteristic`, i.e. the mixed-bidegree gate
`yCap * seedTotalCap < 4064` that binds the whole certificate.

Here the hypothesis is replaced by the Frobenius descent:

* `D` — the closure in the separable part `M`, finite by Mathlib's theorem
  used where it is legitimate (`finite_integralClosure_of_separable`);
* `C ^ q ⊆ D` — because `x ^ q ∈ M` for every `x` (the uniform inseparable
  exponent) and `x ^ q` is still integral;
* `C ^ q` is a finite `A₀`-module — `finite_of_le_restrictScalars`;
* `C ≃+ C ^ q` semilinearly over `σ` — `powEquiv`, `powEquiv_smul`;
* so `C` is a finite `A`-module — `finite_of_semilinear_equiv`.

* `integralClosure_finite_of_frobenius` — the statement.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibInseparableFinite

open LocalMathlibPowImage LocalMathlibFrobeniusDescent LocalMathlibSeparablePartFinite

set_option linter.unusedSectionVars false

variable {A F L : Type*} [CommRing A] [IsDomain A] [Field F] [Field L]
variable [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
variable [IsScalarTower A F L] [FiniteDimensional F L]
variable [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- `A₀ ⊆ A` acts on `A`. -/
@[reducible] noncomputable def subringAlgebra (A₀ : Subring A) : Algebra A₀ A :=
  A₀.subtype.toAlgebra

attribute [local instance] subringAlgebra algebraA₀

theorem subring_tower (A₀ : Subring A) : IsScalarTower A₀ A L :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] subring_tower

/-- **The integral closure is finite, with no separability hypothesis.**

`D` is the finite module the separable part supplies — at the intended
instance, the image in `L` of the integral closure of `A` in
`separableClosure F L`, finite by `finite_integralClosure_of_separable`.
`hCD` is `C ^ q ⊆ D`, which holds because `x ^ q` lands in the separable
part (the uniform inseparable exponent) and stays integral.

Everything else is the Frobenius descent: `C ^ q` is a finite `A₀`-module,
and `C ≃+ C ^ q` semilinearly over `σ`. -/
theorem integralClosure_finite_of_frobenius
    (p e : ℕ) [ExpChar L p]
    (A₀ : Subring A) (σ : A ≃+* A₀) (hσ : ∀ a : A, ((σ a : A)) = a ^ p ^ e)
    (hA₀ : IsNoetherianRing A₀) (hfin : Module.Finite A₀ A)
    (D : Submodule A L) (hD : Module.Finite A D)
    (hCD : ∀ x ∈ integralClosure A L, x ^ p ^ e ∈ D) :
    Module.Finite A (integralClosure A L) := by
  haveI := hA₀
  haveI := hfin
  haveI := hD
  refine finite_of_frobenius_descent (A₀ := A₀) _ D
    (powImage p e A₀ σ hσ (integralClosure A L)) ?_ σ
    (powEquiv p e A₀ σ hσ (integralClosure A L)) (powEquiv_smul p e A₀ σ hσ _)
  rintro y ⟨x, hx, rfl⟩
  exact hCD x hx

end ProximityPrize.SubmissionLower.LocalMathlibInseparableFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInseparableFinite.integralClosure_finite_of_frobenius
