/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# The integral closure is Dedekind without any separability hypothesis

`Mathlib.RingTheory.DedekindDomain.IntegralClosure` proves
`IsIntegralClosure.isDedekindDomain` under a section variable
`[Algebra.IsSeparable K L]`.  Separability is used there for exactly one of
the three components — `IsIntegralClosure.isNoetherianRing`, which goes
through the trace form and so needs the extension separable.  The other two
components, `Ring.DimensionLEOne.of_isIntegral` and integral closedness,
never mention it.

That single use is avoidable: Noetherianity of `C` follows from
`Module.Finite A C` and `IsNoetherianRing A` directly, with no trace form.
So the honest hypothesis is **module-finiteness of the integral closure**,
not separability of the extension — a strictly weaker and more targeted
obligation, and one that is TRUE for the inseparable case over a perfect
base field.

* `isDedekindDomain_of_moduleFinite` — the separability-free replacement.

Why this matters here.  `ContactSurfaceSeedCount` reaches
`CoordinatePoleMass.sum_poles_infinityValues_eq_finrank`, which needs
`IsDedekindDomain (InfiniteNormalization K L)` and `Module.Finite`, and the
only route currently available to that is via separability of the coordinate
projection.  Demanding it is what produces
`ContactProjectionParameters.all_projection_caps_below_characteristic`,
i.e. the mixed-bidegree gate `yCap * seedTotalCap < 4064` that binds the
whole certificate.  Note `Ideal.sum_ramification_inertia` itself has NO
separability hypothesis — it asks for `[IsDedekindDomain S] [Module.Finite R S]`,
which is precisely what this file supplies once finiteness is available.

This module proves a commutative-algebra replacement lemma only.  It is not
a `ProtocolClaim`, an alignment bound, or a submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibDedekindNoSeparable

set_option linter.overlappingInstances false

/-- **The integral closure is Dedekind, with no separability hypothesis.**
Mathlib's `IsIntegralClosure.isDedekindDomain` assumes
`Algebra.IsSeparable K L`, but uses it only to get `IsNoetherianRing C` via
the trace form.  Module-finiteness delivers that directly, so it is the
genuine hypothesis. -/
theorem isDedekindDomain_of_moduleFinite
    (A : Type*) (K : Type*) (L : Type*) (C : Type*)
    [CommRing A] [Field K] [Field L] [CommRing C] [IsDomain C]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
    [FiniteDimensional K L] [IsDedekindDomain A] [Module.Finite A C] :
    IsDedekindDomain C := by
  have hfrac : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have hint : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have hnoeth : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  exact
    { hnoeth, Ring.DimensionLEOne.of_isIntegral A C,
      (isIntegrallyClosed_iff L).mpr fun {x} hx =>
        ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
          IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

end ProximityPrize.SubmissionLower.LocalMathlibDedekindNoSeparable

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibDedekindNoSeparable.isDedekindDomain_of_moduleFinite
