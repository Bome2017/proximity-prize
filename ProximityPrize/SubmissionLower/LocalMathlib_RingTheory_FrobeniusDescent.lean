/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_UniformInseparableExponent

/-!
# The Frobenius descent step

Fifth unit of the separability-free finiteness chain, and the piece that
joins the previous four.

Recall the shape of the descent.  With `q = p ^ e` the uniform inseparable
exponent, `M` the separable closure of `F` in `L`, and `D` the integral
closure of `A` in `M`:

* `D` is finite over `A` — Mathlib's separable case, since `M / F` is
  separable;
* `A` is finite over `A₀ = A ^ q` — `LocalMathlib_RingTheory_ExpandFinite`;
* `C ^ q ⊆ D`, and `C ^ q` is an `A₀`-submodule;
* `A₀` is Noetherian, so `C ^ q` is a finite `A₀`-module — **this file**;
* Frobenius is a semilinear isomorphism `(A, C) → (A₀, C ^ q)`, so
  `LocalMathlib_RingTheory_SemilinearFinite` carries finiteness back to `C`.

Everything happens inside `L`; no compositum and no `F ^ (1/q)` is
constructed, which is what makes the route cheap.

* `finite_of_le_restrictScalars` — an `A₀`-submodule contained in a finite
  `A`-module is a finite `A₀`-module, when `A` is finite over the Noetherian
  `A₀`.  This is the step that turns `C ^ q ⊆ D` into finiteness.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibFrobeniusDescent

variable {A₀ A L : Type*} [CommRing A₀] [CommRing A] [CommRing L]
variable [Algebra A₀ A] [Algebra A L] [Algebra A₀ L] [IsScalarTower A₀ A L]

/-- **The descent step.**  If `A` is a finite module over the Noetherian
`A₀`, and `D` is a finite `A`-submodule of `L`, then any `A₀`-submodule of
`L` contained in `D` is a finite `A₀`-module. -/
theorem finite_of_le_restrictScalars [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (D : Submodule A L) [Module.Finite A D]
    (N : Submodule A₀ L) (hN : ∀ x ∈ N, x ∈ D) :
    Module.Finite A₀ N := by
  classical
  -- `D` is finite over `A₀` by transitivity through `A`, hence Noetherian
  haveI hDA₀ : Module.Finite A₀ D := Module.Finite.trans A D
  haveI hnoeth : IsNoetherian A₀ D := isNoetherian_of_isNoetherianRing_of_finite A₀ _
  -- the `A₀`-linear inclusion `N → D`
  let f : N →ₗ[A₀] D :=
    { toFun := fun x => ⟨x.1, hN x.1 x.2⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : ((f a : D) : L) = ((f b : D) : L) := congrArg (fun z : D => (z : L)) hab
    exact Subtype.ext h1
  haveI : IsNoetherian A₀ N := isNoetherian_of_injective f hf
  exact ⟨IsNoetherian.noetherian ⊤⟩

/-- **Frobenius descent, assembled.**  Reduces the inseparable case of
finiteness of an integral closure to the separable case.

Read it at the intended instance: `A = K[X]`, `A₀ = K[X ^ q]`, `σ` the
`q`-power map (a ring isomorphism `A ≃+* A₀` by
`LocalMathlib_RingTheory_ExpandFrobenius`, using that `K` is perfect), `A`
finite over `A₀` by `LocalMathlib_RingTheory_ExpandFinite`, `D` the integral
closure of `A` in the separable part `M` (finite by Mathlib's separable
case), `N = C ^ q ⊆ D`, and `τ` the `q`-power map on the closure.  The
conclusion is that the closure `C` in `L` is a finite `A`-module — with no
separability hypothesis on `L / F` anywhere. -/
theorem finite_of_frobenius_descent [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (C : Type*) [AddCommGroup C] [Module A C]
    (D : Submodule A L) [Module.Finite A D]
    (N : Submodule A₀ L) (hND : ∀ x ∈ N, x ∈ D)
    (σ : A ≃+* A₀) (τ : C ≃+ N)
    (hc : ∀ (a : A) (c : C), τ (a • c) = σ a • τ c) :
    Module.Finite A C :=
  haveI := finite_of_le_restrictScalars D N hND
  LocalMathlibSemilinearFinite.finite_of_semilinear_equiv σ τ hc

end ProximityPrize.SubmissionLower.LocalMathlibFrobeniusDescent

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibFrobeniusDescent.finite_of_le_restrictScalars
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibFrobeniusDescent.finite_of_frobenius_descent
