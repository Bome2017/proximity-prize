/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SepPartDedekind
import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_UniformInseparableExponent

/-!
# The relative ideal norm of a prime, with no separability hypothesis

The assembly.  `relNorm_prime_eq_pow_of_tower` is instantiated at
`T = sepPart R S F L`:

* `T / R` is separable — `Frac T = separableClosure F L`
  (`isFractionRing_sepPart`), so the project's `SeparableIdealNorm` applies
  after transporting along the canonical fraction-field equivalences;
* `S / T` is purely inseparable — every `x ^ q` lands in the separable
  closure, hence in `T`, which by `eq_of_under_eq` makes the prime above
  unique.

* `relNorm_prime_eq_pow_no_separable`.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibNoSeparableIdealNorm

open LocalMathlibSeparablePartRing LocalMathlibSepPartFractionRing
open LocalMathlibSepPartDedekind LocalMathlibInseparableIdealNorm

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

attribute [local instance] FractionRing.liftAlgebra

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
variable (F L : Type*) [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L] [Algebra F L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R F L]
variable [FiniteDimensional F L] [FaithfulSMul R S] [NoZeroSMulDivisors R S]

instance faithful_sepPart : FaithfulSMul R (sepPart R S F L) := by
  refine (faithfulSMul_iff_algebraMap_injective R _).mpr (fun x y h => ?_)
  refine FaithfulSMul.algebraMap_injective R S ?_
  exact congrArg Subtype.val h

instance faithful_sepPart_frac : FaithfulSMul R (FractionRing (sepPart R S F L)) := by
  refine (faithfulSMul_iff_algebraMap_injective R _).mpr (fun x y h => ?_)
  refine FaithfulSMul.algebraMap_injective R (sepPart R S F L) ?_
  refine IsFractionRing.injective (sepPart R S F L) (FractionRing (sepPart R S F L)) ?_
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact h

/-- The separable part is separable over the base, in the `FractionRing`
form the ideal-norm theorem expects. -/
theorem sepPart_separable :
    Algebra.IsSeparable (FractionRing R) (FractionRing (sepPart R S F L)) := by
  haveI : Algebra.IsSeparable F (separableClosure F L) :=
    separableClosure.isSeparable F L
  apply Algebra.IsSeparable.of_equiv_equiv
    (A₁ := F) (B₁ := separableClosure F L)
    (A₂ := FractionRing R) (B₂ := FractionRing (sepPart R S F L))
    (FractionRing.algEquiv R F).symm.toRingEquiv
    (FractionRing.algEquiv (sepPart R S F L) (separableClosure F L)).symm.toRingEquiv
  ext y
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R F).symm
    (FractionRing.algEquiv (sepPart R S F L) (separableClosure F L)).symm y

instance noZeroSMul_sepPart : NoZeroSMulDivisors (sepPart R S F L) S := by
  constructor
  intro c x h
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with hc | hx
  · left
    exact Subtype.ext hc
  · right
    exact hx

/-- **The relative ideal norm of a prime, with no separability hypothesis.** -/
theorem relNorm_prime_eq_pow_no_separable
    (q : ℕ) (hq : 0 < q) (hexp : ∀ x : L, x ^ q ∈ separableClosure F L)
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hPT : (P.under (sepPart R S F L)) ≠ ⊥)
    [(P.under (sepPart R S F L)).IsMaximal]
    [(P.under (sepPart R S F L)).LiesOver p] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  haveI := sepPart_separable R S F L
  -- `S / T` is purely inseparable
  have hpi : ∀ x : S, ∃ t : sepPart R S F L,
      algebraMap (sepPart R S F L) S t = x ^ q := by
    intro x
    have hmem : x ^ q ∈ sepPart R S F L := by
      show algebraMap S L (x ^ q) ∈ separableClosure F L
      rw [map_pow]
      exact hexp _
    exact ⟨⟨x ^ q, hmem⟩, rfl⟩
  -- `T / R` is separable, so the existing separable theorem applies at `T`
  have hsep : Ideal.relNorm R (P.under (sepPart R S F L))
      = p ^ (P.under (sepPart R S F L)).inertiaDeg R :=
    SeparableIdealNorm.relNorm_prime_eq_pow R (sepPart R S F L)
      (P.under (sepPart R S F L)) p
  exact relNorm_prime_eq_pow_of_tower R S (sepPart R S F L) q hq hpi p hp P hPT hsep

include F L in
/-- **The relative ideal norm of a prime, with the characteristic eliminated.**

No separability and no extra hypotheses: in characteristic zero every
algebraic extension is separable so the old proof applies, and in
characteristic `p` the uniform inseparable exponent feeds
`relNorm_prime_eq_pow_no_separable`.  This is therefore a drop-in
replacement for `SeparableIdealNorm.relNorm_prime_eq_pow` that costs its
callers nothing. -/
theorem relNorm_prime_eq_pow_general
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  classical
  haveI : (P.under (sepPart R S F L)).LiesOver p :=
    Ideal.LiesOver.tower_bot P (P.under (sepPart R S F L)) p
  haveI : (P.under (sepPart R S F L)).IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (P.under (sepPart R S F L)) p
  have hPT : (P.under (sepPart R S F L)) ≠ ⊥ := by
    intro hcon
    apply hp
    have h : p = Ideal.under R (P.under (sepPart R S F L)) := Ideal.LiesOver.over
    rw [hcon] at h
    simpa using h
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hchar | hchar
  · -- characteristic `p`: use the uniform inseparable exponent
    haveI : Fact (ringChar F).Prime := ⟨hchar⟩
    haveI : CharP F (ringChar F) := ringChar.charP F
    haveI : ExpChar F (ringChar F) := ExpChar.prime hchar
    haveI : CharP L (ringChar F) :=
      charP_of_injective_algebraMap (algebraMap F L).injective (ringChar F)
    haveI : ExpChar L (ringChar F) := ExpChar.prime hchar
    haveI : CharP (separableClosure F L) (ringChar F) :=
      charP_of_injective_algebraMap
        (algebraMap F (separableClosure F L)).injective (ringChar F)
    haveI : ExpChar (separableClosure F L) (ringChar F) := ExpChar.prime hchar
    haveI : IsPurelyInseparable (separableClosure F L) L :=
      separableClosure.isPurelyInseparable F L
    haveI : FiniteDimensional (separableClosure F L) L :=
      FiniteDimensional.right F (separableClosure F L) L
    obtain ⟨e, he⟩ := LocalMathlibUniformInseparableExponent.exists_uniform_exponent
      (separableClosure F L) L (ringChar F)
    refine relNorm_prime_eq_pow_no_separable R S F L ((ringChar F) ^ e)
      (pow_pos hchar.pos e) (fun x => ?_) p hp P hPT
    obtain ⟨y, hy⟩ := he x
    rw [← hy]
    exact y.2
  · -- characteristic zero: the extension is automatically separable
    haveI : CharP F 0 := hchar ▸ ringChar.charP F
    haveI : CharZero F := CharP.charP_to_charZero F
    haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
    haveI : Algebra.IsSeparable F L := inferInstance
    refine relNorm_prime_eq_pow_no_separable R S F L 1 one_pos (fun x => ?_) p hp P hPT
    rw [pow_one]
    exact mem_separableClosure_iff.mpr (Algebra.IsSeparable.isSeparable F x)

end ProximityPrize.SubmissionLower.LocalMathlibNoSeparableIdealNorm

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibNoSeparableIdealNorm.sepPart_separable

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibNoSeparableIdealNorm.relNorm_prime_eq_pow_no_separable
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibNoSeparableIdealNorm.relNorm_prime_eq_pow_general
