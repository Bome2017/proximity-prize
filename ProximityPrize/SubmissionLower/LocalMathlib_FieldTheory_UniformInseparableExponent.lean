/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SemilinearFinite

/-!
# A uniform inseparable exponent for a finite purely inseparable extension

Fourth unit of the separability-free finiteness chain.

`IsPurelyInseparable.pow_mem` gives, for each `x : E`, SOME `n` with
`x ^ q ^ n` in the base.  The Frobenius descent needs one exponent that works
for every `x` at once — that is what turns "`L` is purely inseparable over its
separable closure `M`" into the usable "`L ^ q ⊆ M`".

* `exists_uniform_exponent` — for `E / F` finite and purely inseparable there
  is a single `e` with `x ^ q ^ e ∈ (algebraMap F E).range` for all `x`.

The proof is the natural one and uses finiteness exactly once: take a finite
spanning set, take the maximum of its per-element exponents, and observe that
`{x | x ^ q ^ e ∈ range}` is an `F`-submodule — closed under addition by the
freshman's dream `(x + y) ^ q ^ e = x ^ q ^ e + y ^ q ^ e`, and under scalars
because `c ^ q ^ e` is again in the base.  A submodule containing a spanning
set is everything.

Mathlib has the per-element version but not this one (checked).

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibUniformInseparableExponent

set_option linter.unusedSectionVars false

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (q : ℕ)

/-- The elements killed into the base by the fixed exponent `e` form an
`F`-submodule. -/
def exponentSubmodule [ExpChar E q] (e : ℕ) : Submodule F E where
  carrier := {x : E | x ^ q ^ e ∈ (algebraMap F E).range}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, add_pow_expChar_pow]
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [map_zero, zero_pow (pow_ne_zero e (expChar_ne_zero E q))]
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    refine ⟨c ^ q ^ e * a, ?_⟩
    rw [map_mul, map_pow, ha, Algebra.smul_def, mul_pow]

theorem mem_exponentSubmodule_iff [ExpChar E q] (e : ℕ) (x : E) :
    x ∈ exponentSubmodule F E q e ↔ x ^ q ^ e ∈ (algebraMap F E).range := Iff.rfl

/-- Raising the exponent keeps membership. -/
theorem exponentSubmodule_mono [ExpChar E q] {d e : ℕ} (h : d ≤ e) :
    exponentSubmodule F E q d ≤ exponentSubmodule F E q e := by
  rintro x ⟨a, ha⟩
  refine ⟨a ^ q ^ (e - d), ?_⟩
  have hpow : q ^ e = q ^ d * q ^ (e - d) := by
    rw [← pow_add]
    congr 1
    omega
  rw [map_pow, ha, ← pow_mul, ← hpow]

/-- **A uniform inseparable exponent.**  Finiteness is used exactly once, to
take the maximum over a spanning set. -/
theorem exists_uniform_exponent [ExpChar F q] [ExpChar E q]
    [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ e : ℕ, ∀ x : E, x ^ q ^ e ∈ (algebraMap F E).range := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := F) (M := E)
  -- a per-element exponent for each spanning vector
  have hex : ∀ x : E, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := fun x =>
    IsPurelyInseparable.pow_mem F q x
  choose n hn using hex
  refine ⟨s.sup n, fun x => ?_⟩
  -- the submodule at the maximal exponent contains the spanning set
  have hsub : ∀ y ∈ s, y ∈ exponentSubmodule F E q (s.sup n) := by
    intro y hy
    exact exponentSubmodule_mono F E q (Finset.le_sup hy) (hn y)
  have hspan : Submodule.span F (s : Set E) ≤ exponentSubmodule F E q (s.sup n) :=
    Submodule.span_le.mpr hsub
  rw [hs] at hspan
  exact hspan (Submodule.mem_top)

end ProximityPrize.SubmissionLower.LocalMathlibUniformInseparableExponent

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibUniformInseparableExponent.exists_uniform_exponent
