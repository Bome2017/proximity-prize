/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_InseparableIdealNorm

/-!
# The separable part of an integral closure, as a subalgebra

`relNorm_prime_eq_pow_of_tower` takes the tower `R ⊆ T ⊆ S` as a hypothesis.
This file builds `T`.

Taking `T` to be the PREIMAGE IN `S` of `separableClosure (Frac R) (Frac S)`
— rather than `integralClosure R (separableClosure …)` — makes it a
`Subalgebra R S` outright, so the algebra map `T → S` is the inclusion and
no lifting is needed.

The two finiteness facts the tower needs come free from `Module.Finite R S`:

* `Module.Finite R T` — `T` is a submodule of the finite module `S` over the
  Noetherian `R`;
* `Module.Finite T S` — the `R`-generators of `S` also generate over `T`.

* `sepPart` — the subalgebra;
* `sepPart_finite`, `finite_over_sepPart` — the two finiteness facts.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSeparablePartRing

set_option linter.unusedSectionVars false

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
variable (F L : Type*) [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L] [Algebra F L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R F L]

/-- The separable part of `S`: the elements whose image in `L` is separable
over `F`.  A subalgebra of `S`, so the map to `S` is the inclusion. -/
def sepPart : Subalgebra R S :=
  Subalgebra.comap (IsScalarTower.toAlgHom R S L)
    ((separableClosure F L).toSubalgebra.restrictScalars R)

theorem mem_sepPart_iff (x : S) :
    x ∈ sepPart R S F L ↔ (algebraMap S L x) ∈ separableClosure F L := Iff.rfl

/-- `T` is a finite `R`-module: it is a submodule of the finite module `S`
over the Noetherian ring `R`. -/
instance sepPart_finite : Module.Finite R (sepPart R S F L) := by
  haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S
  exact Module.Finite.of_injective
    (Submodule.subtype (Subalgebra.toSubmodule (sepPart R S F L)))
    Subtype.val_injective

/-- `S` is a finite `T`-module: the `R`-generators of `S` generate over the
larger ring `T`. -/
instance finite_over_sepPart : Module.Finite (sepPart R S F L) S :=
  Module.Finite.of_restrictScalars_finite R _ S

end ProximityPrize.SubmissionLower.LocalMathlibSeparablePartRing

#print axioms ProximityPrize.SubmissionLower.LocalMathlibSeparablePartRing.sepPart_finite
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSeparablePartRing.finite_over_sepPart
