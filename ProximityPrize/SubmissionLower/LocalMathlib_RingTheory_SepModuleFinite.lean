/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SepModule

/-!
# `sepIntegral` is a finite `A`-module

Eleventh unit: the last obligation in the chain.

`sepIntegral A F L` is spanned by the elements of `L` lying in the separable
closure and integral over `A`.  That set is exactly the image of
`integralClosure A M` (`M = separableClosure F L`) under the inclusion
`M ↪ L`, because integrality transfers along an injective algebra map.  The
closure in `M` is finite by Mathlib's separable theorem
(`finite_integralClosure_of_separable`), and the image of a finitely
generated module is finitely generated.

* `sepIntegralSet_eq_image` — the set identification;
* `sepIntegral_finite` — hence `Module.Finite A (sepIntegral A F L)`.

With this the chain closes: every hypothesis of
`integralClosure_finite_of_frobenius` is discharged, so the integral closure
is finite with no separability hypothesis on `L / F`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSepModuleFinite

open LocalMathlibSepModule LocalMathlibSeparablePartFinite

set_option linter.unusedSectionVars false

variable {A F L : Type*} [CommRing A] [IsDomain A] [Field F] [Field L]
variable [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
variable [IsScalarTower A F L] [FiniteDimensional F L]
variable [IsIntegrallyClosed A] [IsNoetherianRing A]

instance sepTowerAML : IsScalarTower A (separableClosure F L) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The inclusion of the separable closure, as an `A`-algebra map. -/
noncomputable def sepVal : separableClosure F L →ₐ[A] L :=
  IsScalarTower.toAlgHom A (separableClosure F L) L

theorem sepVal_injective : Function.Injective (sepVal (A := A) (F := F) (L := L)) := by
  intro x y h
  exact Subtype.ext h

/-- **The set identification.**  Integrality transfers along the injective
inclusion, so the elements of `L` that are separable and integral are exactly
the image of the integral closure in the separable part. -/
theorem sepIntegralSet_eq_image :
    sepIntegralSet A F L =
      (sepVal (A := A) (F := F) (L := L)) ''
        {z : separableClosure F L | IsIntegral A z} := by
  ext y
  constructor
  · rintro ⟨hyM, hyint⟩
    refine ⟨⟨y, hyM⟩, ?_, rfl⟩
    exact (isIntegral_algHom_iff (sepVal (A := A) (F := F) (L := L))
      sepVal_injective).mp hyint
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, (isIntegral_algHom_iff (sepVal (A := A) (F := F) (L := L))
      sepVal_injective).mpr hz⟩

/-- **`sepIntegral` is a finite `A`-module.** -/
theorem sepIntegral_finite : Module.Finite A (sepIntegral A F L) := by
  haveI hfin : Module.Finite A (integralClosure A (separableClosure F L)) :=
    finite_integralClosure_of_separable (A := A) (F := F) (L := L) _
  have hset : sepIntegral A F L =
      Submodule.map (sepVal (A := A) (F := F) (L := L)).toLinearMap
        (Subalgebra.toSubmodule (integralClosure A (separableClosure F L))) := by
    rw [sepIntegral, sepIntegralSet_eq_image]
    rw [show ((sepVal (A := A) (F := F) (L := L)) ''
          {z : separableClosure F L | IsIntegral A z})
        = ((sepVal (A := A) (F := F) (L := L)).toLinearMap ''
            (↑(Subalgebra.toSubmodule
              (integralClosure A (separableClosure F L))) : Set _)) from rfl]
    rw [← Submodule.map_span, Submodule.span_eq]
  rw [hset]
  exact Module.Finite.map _ _

end ProximityPrize.SubmissionLower.LocalMathlibSepModuleFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSepModuleFinite.sepIntegral_finite
