/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SepPartFractionRing
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_DedekindDomain_NoSeparable

/-!
# The separable part is a Dedekind domain

`sepPart R S F L` is the integral closure of `R` in `separableClosure F L`:
it is integral over `R` (being inside `S`), and conversely any element of the
separable closure integral over `R` lies in `S` (integrally closed) and is
separable, hence lies in `sepPart`.

With that, `isDedekindDomain_of_moduleFinite` applies — and it applies with
NO separability hypothesis, which is the point of that lemma.

* `isIntegralClosure_sepPart`;
* `isDedekindDomain_sepPart`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSepPartDedekind

open LocalMathlibSeparablePartRing LocalMathlibSepPartFractionRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
variable (F L : Type*) [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L] [Algebra F L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R F L]
variable [IsIntegrallyClosed S] [FiniteDimensional F L]

instance towerRML : IsScalarTower R (separableClosure F L) L :=
  IsScalarTower.of_algebraMap_eq' rfl

instance towerRTM : IsScalarTower R (sepPart R S F L) (separableClosure F L) := by
  refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
  apply Subtype.ext
  show ((algebraMap R (separableClosure F L) r : separableClosure F L) : L)
    = algebraMap S L (algebraMap R S r)
  rw [← IsScalarTower.algebraMap_apply R S L]
  rfl

/-- `sepPart` is the integral closure of `R` in the separable closure. -/
instance isIntegralClosure_sepPart :
    IsIntegralClosure (sepPart R S F L) R (separableClosure F L) where
  algebraMap_injective := by
    intro x y h
    exact toClosure_injective R S F L h
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      -- integral over `R`, hence over `S`, hence in `S`
      have hxL : IsIntegral R ((x : separableClosure F L) : L) := by
        have := hx.map (IsScalarTower.toAlgHom R (separableClosure F L) L)
        simpa using this
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S)).mp hxL.tower_top
      have hmem : a ∈ sepPart R S F L := by
        show algebraMap S L a ∈ separableClosure F L
        rw [ha]
        exact x.2
      exact ⟨⟨a, hmem⟩, by apply Subtype.ext; exact ha⟩
    · rintro ⟨y, rfl⟩
      -- everything in `sepPart` is integral over `R`, being inside `S`
      have hS : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
      have h1 : IsIntegral R (algebraMap S L (y : S)) :=
        (hS.isIntegral (y : S)).map (IsScalarTower.toAlgHom R S L)
      have h2 : IsIntegral R
          ((algebraMap (sepPart R S F L) (separableClosure F L) y :
            separableClosure F L) : L) := by
        rw [algebraMap_toClosure]
        exact h1
      exact (isIntegral_algHom_iff
        (IsScalarTower.toAlgHom R (separableClosure F L) L)
        (fun a b hab => Subtype.ext hab)).mp h2

variable [IsDedekindDomain R]

/-- **The separable part is a Dedekind domain** — via
`isDedekindDomain_of_moduleFinite`, so with no separability hypothesis. -/
instance isDedekindDomain_sepPart : IsDedekindDomain (sepPart R S F L) := by
  haveI : FiniteDimensional F (separableClosure F L) :=
    FiniteDimensional.left F (separableClosure F L) L
  exact LocalMathlibDedekindNoSeparable.isDedekindDomain_of_moduleFinite
    R F (separableClosure F L) (sepPart R S F L)

end ProximityPrize.SubmissionLower.LocalMathlibSepPartDedekind

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSepPartDedekind.isDedekindDomain_sepPart
