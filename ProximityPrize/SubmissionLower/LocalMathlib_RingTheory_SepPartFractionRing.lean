/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SeparablePartRing

/-!
# The separable part has the separable closure as its fraction field

`sepPart R S F L` is the elements of `S` separable over `F`.  Its fraction
field, inside `L`, is exactly `separableClosure F L`: given a separable `y`,
`Algebra.IsAlgebraic.exists_integral_multiple` clears denominators to make
`d • y` integral, and `d • y` is still separable, so it lies in `sepPart`,
whence `y = (d • y) / d` with both in `sepPart`.

This is what lets the separable case of the ideal-norm formula be applied at
`T = sepPart`, which is the remaining hypothesis of
`relNorm_prime_eq_pow_of_tower`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSepPartFractionRing

open LocalMathlibSeparablePartRing

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
variable (F L : Type*) [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L] [Algebra F L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R F L]

/-- The separable part maps into the separable closure. -/
def toClosure : sepPart R S F L →+* separableClosure F L where
  toFun x := ⟨algebraMap S L x.1, x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp

theorem toClosure_coe (x : sepPart R S F L) :
    ((toClosure R S F L x : separableClosure F L) : L) = algebraMap S L (x : S) := rfl

theorem toClosure_injective : Function.Injective (toClosure R S F L) := by
  intro x y h
  have h1 : algebraMap S L (x : S) = algebraMap S L (y : S) :=
    congrArg (fun z : separableClosure F L => (z : L)) h
  exact Subtype.ext (IsFractionRing.injective S L h1)

noncomputable instance algebraToClosure :
    Algebra (sepPart R S F L) (separableClosure F L) :=
  (toClosure R S F L).toAlgebra

theorem algebraMap_toClosure (x : sepPart R S F L) :
    ((algebraMap (sepPart R S F L) (separableClosure F L) x : separableClosure F L) : L)
      = algebraMap S L (x : S) := rfl

variable [IsIntegrallyClosed S] [FiniteDimensional F L]

/-- `R` lands in the separable part. -/
theorem algebraMap_mem_sepPart (d : R) : algebraMap R S d ∈ sepPart R S F L := by
  show algebraMap S L (algebraMap R S d) ∈ separableClosure F L
  rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R F L]
  exact (separableClosure F L).algebraMap_mem _

/-- **The separable closure is the fraction field of the separable part.** -/
instance isFractionRing_sepPart :
    IsFractionRing (sepPart R S F L) (separableClosure F L) where
  map_units := by
    rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr ?_
    intro hzero
    refine (mem_nonZeroDivisors_iff_ne_zero.mp hy) (toClosure_injective R S F L ?_)
    rw [map_zero]
    exact hzero
  surj := by
    intro z
    have hzL : ((z : separableClosure F L) : L) ∈ separableClosure F L := z.2
    have halg : IsAlgebraic R ((z : separableClosure F L) : L) := by
      haveI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
      exact (IsFractionRing.isAlgebraic_iff R F L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨d, hd0, hint⟩ := IsAlgebraic.exists_integral_multiple halg
    -- the multiple is integral over `S`, hence in `S`
    have hintS : IsIntegral S (d • ((z : separableClosure F L) : L)) := hint.tower_top
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S)).mp hintS
    -- and still separable, hence in the separable part
    have hmem : a ∈ sepPart R S F L := by
      show algebraMap S L a ∈ separableClosure F L
      rw [ha, Algebra.smul_def, IsScalarTower.algebraMap_apply R F L]
      exact mul_mem ((separableClosure F L).algebraMap_mem _) hzL
    have hdmem : algebraMap R S d ∈ sepPart R S F L := algebraMap_mem_sepPart R S F L d
    have hdnz : (⟨algebraMap R S d, hdmem⟩ : sepPart R S F L) ∈ nonZeroDivisors _ := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hcon
      apply hd0
      have : algebraMap R S d = 0 := congrArg Subtype.val hcon
      have hinjRL : Function.Injective (algebraMap R L) := by
        rw [IsScalarTower.algebraMap_eq R F L]
        exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
      apply hinjRL
      rw [IsScalarTower.algebraMap_apply R S L, this, map_zero, map_zero]
    refine ⟨(⟨a, hmem⟩, ⟨⟨algebraMap R S d, hdmem⟩, hdnz⟩), ?_⟩
    apply Subtype.ext
    show ((z : separableClosure F L) : L) * algebraMap S L (algebraMap R S d)
      = algebraMap S L a
    rw [ha, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R S L]
    ring
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using toClosure_injective R S F L h⟩

end ProximityPrize.SubmissionLower.LocalMathlibSepPartFractionRing

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSepPartFractionRing.toClosure_injective
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSepPartFractionRing.isFractionRing_sepPart
