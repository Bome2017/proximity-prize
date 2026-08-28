/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_ExpandFinite

/-!
# `K[X] ^ q = K[X ^ q]` over a perfect field

Second unit of the separability-free finiteness chain.

The purely-inseparable base change needs the `q`-th power map on `K[X]` to
land exactly on the subring `K[X ^ q]` of
`LocalMathlib_RingTheory_ExpandFinite`.  Both inclusions are here:

* `pow_eq_expand_map` — `f ^ q = expand K q (f.map (iterateFrobenius K p e))`
  for `q = p ^ e`.  Both sides are ring homomorphisms of `K[X]`, so it is
  enough to check them on `C a` and on `X`;
* `pow_mem_expandRange` — hence `f ^ q ∈ K[X ^ q]`, in ANY characteristic `p`;
* `exists_pow_eq_of_mem_expandRange` — conversely, over a perfect `K` every
  element of `K[X ^ q]` is a `q`-th power, because `iterateFrobenius K p e`
  is then bijective.

Perfectness is used only for the converse, which is exactly where it is
genuinely needed: `K[X ^ q] ⊆ K[X] ^ q` fails for imperfect `K`.

Together these say the `q`-power map carries `K[X]` isomorphically onto
`K[X ^ q]`, which is what lets the Frobenius transfer the finiteness of an
integral closure back down.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibExpandFrobenius

open Polynomial LocalMathlibExpandFinite

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

-- `Polynomial.Bivariate` rebinds bare `X`; everything is fully qualified.

variable (K : Type*) [CommRing K] [Nontrivial K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p]

instance charP_polynomial : CharP (Polynomial K) p :=
  charP_of_injective_ringHom (Polynomial.C_injective (R := K)) p

instance expChar_polynomial : ExpChar (Polynomial K) p :=
  ExpChar.prime hp.out

instance expChar_base : ExpChar K p := ExpChar.prime hp.out

/-- **The Frobenius identity.**  `f ^ (p ^ e)` is the `expand` of the
coefficientwise Frobenius.  Both sides are ring homomorphisms, so it suffices
to check `C a` and `X`. -/
theorem pow_eq_expand_map (f : Polynomial K) :
    f ^ p ^ e =
      Polynomial.expand K (p ^ e) (f.map (iterateFrobenius K p e)) := by
  have h : (iterateFrobenius (Polynomial K) p e : Polynomial K →+* Polynomial K) =
      (Polynomial.expand K (p ^ e)).toRingHom.comp
        (Polynomial.mapRingHom (iterateFrobenius K p e)) := by
    apply Polynomial.ringHom_ext
    · intro a
      show (Polynomial.C a) ^ p ^ e = _
      simp [Polynomial.C_pow, iterateFrobenius_def]
    · show (Polynomial.X : Polynomial K) ^ p ^ e = _
      simp [iterateFrobenius_def]
  have hf := congrArg (fun φ : Polynomial K →+* Polynomial K => φ f) h
  simpa [iterateFrobenius_def] using hf

/-- `f ^ q` always lies in `K[X ^ q]`. -/
theorem pow_mem_expandRange (f : Polynomial K) :
    f ^ p ^ e ∈ expandRange K (p ^ e) :=
  ⟨f.map (iterateFrobenius K p e), (pow_eq_expand_map K p e f).symm⟩

/-- **Conversely, over a perfect field every element of `K[X ^ q]` is a
`q`-th power.**  This is the only place perfectness is used. -/
theorem exists_pow_eq_of_mem_expandRange [PerfectRing K p] (g : Polynomial K)
    (hg : g ∈ expandRange K (p ^ e)) :
    ∃ f : Polynomial K, f ^ p ^ e = g := by
  obtain ⟨h, hh⟩ := hg
  refine ⟨h.map (iterateFrobeniusEquiv K p e).symm.toRingHom, ?_⟩
  rw [pow_eq_expand_map K p e]
  rw [Polynomial.map_map]
  have hcomp : (iterateFrobenius K p e).comp
      (iterateFrobeniusEquiv K p e).symm.toRingHom = RingHom.id K := by
    ext x
    show iterateFrobenius K p e ((iterateFrobeniusEquiv K p e).symm x) = x
    rw [← coe_iterateFrobeniusEquiv]
    exact (iterateFrobeniusEquiv K p e).apply_symm_apply x
  rw [hcomp, Polynomial.map_id]
  exact hh

end ProximityPrize.SubmissionLower.LocalMathlibExpandFrobenius

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandFrobenius.pow_eq_expand_map
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandFrobenius.pow_mem_expandRange
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandFrobenius.exists_pow_eq_of_mem_expandRange
