/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.SeparableIdealNorm
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Basic

/-!
# The relative ideal norm of a prime, purely inseparable case

`SeparableIdealNorm.relNorm_prime_eq_pow` proves `relNorm R P = (P ∩ R) ^ f`
by Galois descent through a normal closure, so it needs separability as a
METHOD.  Mathlib's two versions have the same shape: one assumes `IsGalois`,
the other `PerfectField (FractionRing R)` — used only to make the normal
closure Galois.  For a genuinely inseparable extension there is nothing to
descend along.

The purely inseparable case needs no descent at all, because the prime above
is UNIQUE:

* `eq_of_under_eq` — if `x ^ q` lands in `R` for every `x : S`, then two
  maximal ideals of `S` lying over the same prime of `R` are equal.  For
  `x ∈ P` one gets `x ^ q ∈ P ∩ R = Q ∩ R ⊆ Q`, hence `x ∈ Q`.

With a unique prime the fundamental identity `Σ eᵢ fᵢ = n` collapses to
`e * f = n`, and `relNorm (p.map) = p ^ n` collapses to `p ^ (e * s) = p ^ n`,
so `s = f` is forced — with no separability anywhere.

* `relNorm_prime_eq_pow_of_unique` — the resulting formula.

Composing this with the separable case along the tower
`F ⊆ separableClosure F L ⊆ L` (via `relNorm_relNorm` and `inertiaDeg_tower`)
gives the formula in general.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibInseparableIdealNorm

open Ideal

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S]

/-- **Uniqueness of the prime above, in the purely inseparable case.**
If every `q`-th power in `S` comes from `R`, two maximal ideals over the same
prime coincide. -/
theorem eq_of_under_eq (q : ℕ) (hq : 0 < q)
    (hpi : ∀ x : S, ∃ r : R, algebraMap R S r = x ^ q)
    (P Q : Ideal S) [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (h : P.under R = Q.under R) : P = Q := by
  have hle : P ≤ Q := by
    intro x hx
    obtain ⟨r, hr⟩ := hpi x
    have hxq : x ^ q ∈ P := Ideal.pow_mem_of_mem P hx q hq
    have hrP : r ∈ P.under R := by
      show algebraMap R S r ∈ P
      rw [hr]; exact hxq
    have hrQ : algebraMap R S r ∈ Q := by
      have : r ∈ Q.under R := h ▸ hrP
      exact this
    have : x ^ q ∈ Q := by rw [← hr]; exact hrQ
    exact hQ.isPrime.mem_of_pow_mem q this
  exact (hP.eq_of_le hQ.ne_top hle)

section Norm

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
variable [NoZeroSMulDivisors R S] [IsIntegrallyClosed R] [IsIntegrallyClosed S]
variable [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra
variable (F L : Type*) [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
variable [Algebra S L] [IsFractionRing S L] [Algebra F L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R F L]

/-- With a unique prime above, the set of primes over `p` is a singleton. -/
theorem primesOverFinset_eq_singleton (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [hPp : P.IsPrime] [hPo : P.LiesOver p]
    (hunique : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → Q = P) :
    IsDedekindDomain.primesOverFinset p S = {P} := by
  ext Q
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact hunique Q h1 h2
  · rintro rfl
    exact ⟨hPp, hPo⟩

/-- **The relative ideal norm of a prime, when the prime above is unique.**
No separability: the fundamental identity collapses to `e * f = n`, and
`relNorm (p.map) = p ^ n` collapses to `p ^ (s * e) = p ^ n`. -/
theorem relNorm_prime_eq_pow_of_unique
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hunique : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → Q = P) :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  classical
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  have hsingle := primesOverFinset_eq_singleton R S p hp P hunique
  -- the fundamental identity, with the sum collapsed
  have hn : P.ramificationIdx R * P.inertiaDeg R = Module.finrank (FractionRing R) (FractionRing S) := by
    have h := Ideal.sum_ramification_inertia S (FractionRing R) (FractionRing S) hp
    rw [hsingle, Finset.sum_singleton] at h
    rw [Ideal.ramificationIdx'_eq_ramificationIdx, Ideal.inertiaDeg'_eq_inertiaDeg] at h
    · exact h
    · exact hp
  -- `p S = P ^ e`
  have hset : (p.primesOver S).toFinset = {P} := by
    ext Q
    simp only [Set.mem_toFinset, Finset.mem_singleton, Ideal.primesOver, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact hunique Q h1 h2
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  have hmap : p.map (algebraMap R S) = P ^ P.ramificationIdx R := by
    have h := Ideal.map_algebraMap_eq_finsetProd_pow (R := S) (S := R) (p := p) hp
    rw [hset, Finset.prod_singleton] at h
    exact h
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P p
  have h1 : Ideal.relNorm R (p.map (algebraMap R S)) = p ^ Module.finrank (FractionRing R) (FractionRing S) :=
    Ideal.relNorm_algebraMap S p
  have h2 : Ideal.relNorm R (p.map (algebraMap R S))
      = p ^ (s * P.ramificationIdx R) := by
    rw [hmap, map_pow, hs, ← pow_mul]
  have hkey : p ^ (s * P.ramificationIdx R)
      = p ^ (P.ramificationIdx R * P.inertiaDeg R) := by
    rw [← h2, h1, hn]
  have hpne : (p : Ideal R) ≠ 0 := hp
  have hp1 : (p : Ideal R) ≠ 1 := by
    rw [Ideal.one_eq_top]
    exact Ideal.IsMaximal.ne_top inferInstance
  have hpow : s * P.ramificationIdx R
      = P.ramificationIdx R * P.inertiaDeg R :=
    ((IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hpne).pow_injective hp1) hkey
  have hepos : 0 < P.ramificationIdx R := Ideal.ramificationIdx_pos P R
  rw [hs]
  congr 1
  have hmul : s * P.ramificationIdx R = P.inertiaDeg R * P.ramificationIdx R := by
    rw [hpow]; ring
  exact Nat.eq_of_mul_eq_mul_right hepos hmul

/-- **The relative ideal norm of a prime, in general — no separability.**

The tower `R ⊆ T ⊆ S` is supplied by the caller: `T` is the integral closure
of `R` in the separable closure, so `T / R` is separable (`hsep`, discharged
by `SeparableIdealNorm`) and `S / T` is purely inseparable (`hpi`), which by
`eq_of_under_eq` makes the prime above unique.  Deferring the construction of
`T` keeps the `IntermediateField` instance diamonds out of this layer. -/
theorem relNorm_prime_eq_pow_of_tower
    (T : Type*) [CommRing T] [IsDomain T] [IsDedekindDomain T] [IsIntegrallyClosed T]
    [Algebra R T] [Algebra T S] [IsScalarTower R T S]
    [Module.Finite R T] [Module.Finite T S]
    [Module.IsTorsionFree R T] [Module.IsTorsionFree T S] [NoZeroSMulDivisors T S]
    (q : ℕ) (hq : 0 < q) (hpi : ∀ x : S, ∃ t : T, algebraMap T S t = x ^ q)
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hPT : (P.under T) ≠ ⊥) [(P.under T).IsMaximal]
    (hsep : Ideal.relNorm R (P.under T) = p ^ (P.under T).inertiaDeg R) :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  classical
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  haveI : P.LiesOver (P.under T) := ⟨rfl⟩
  -- `P` is the unique prime of `S` over `P.under T`
  have hunique : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver (P.under T) → Q = P := by
    intro Q hQ hQo
    haveI := hQ
    haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (P.under T)
    exact eq_of_under_eq q hq hpi Q P (by rw [← hQo.over])
  have h1 : Ideal.relNorm T P = (P.under T) ^ P.inertiaDeg T :=
    relNorm_prime_eq_pow_of_unique T S (P.under T) hPT P hunique
  rw [← Ideal.relNorm_relNorm R T P, h1, map_pow, hsep, ← pow_mul,
    ← Ideal.inertiaDeg_tower (R := R) (S := T)]

end Norm

end ProximityPrize.SubmissionLower.LocalMathlibInseparableIdealNorm

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInseparableIdealNorm.eq_of_under_eq
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInseparableIdealNorm.relNorm_prime_eq_pow_of_unique
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInseparableIdealNorm.relNorm_prime_eq_pow_of_tower
