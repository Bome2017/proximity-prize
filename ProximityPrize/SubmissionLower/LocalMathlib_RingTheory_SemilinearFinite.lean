/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_ExpandFrobenius

/-!
# Module-finiteness transfers along a semilinear isomorphism

Third unit of the separability-free finiteness chain.

The Frobenius descent needs exactly this shape.  With `q = p ^ e`, the
`q`-power map carries `K[X]` isomorphically onto `K[X ^ q]`
(`LocalMathlib_RingTheory_ExpandFrobenius`) and carries the integral closure
`C` onto `C ^ q`.  It is a ring isomorphism on the base and only a SEMILINEAR
bijection on the module, so no ordinary `Module.Finite` transport applies.

* `finite_of_semilinear_equiv` — if `σ : R ≃+* R'` and `τ : M ≃+ M'` satisfy
  `τ (r • m) = σ r • τ m`, then `Module.Finite R' M'` gives `Module.Finite R M`.

The proof is the obvious one: pull a finite `R'`-generating set of `M'` back
through `τ`, and rewrite each `R'`-coefficient as `σ.symm` of itself.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibSemilinearFinite

variable {R R' M M' : Type*}
variable [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R' M']

/-- `τ.symm` is semilinear for `σ.symm` whenever `τ` is semilinear for `σ`. -/
theorem symm_smul (σ : R ≃+* R') (τ : M ≃+ M')
    (hc : ∀ (r : R) (m : M), τ (r • m) = σ r • τ m) (r' : R') (y : M') :
    τ.symm (r' • y) = σ.symm r' • τ.symm y := by
  apply τ.injective
  rw [τ.apply_symm_apply, hc, σ.apply_symm_apply, τ.apply_symm_apply]

/-- **Finiteness transfers along a semilinear isomorphism.** -/
theorem finite_of_semilinear_equiv [Module.Finite R' M']
    (σ : R ≃+* R') (τ : M ≃+ M')
    (hc : ∀ (r : R) (m : M), τ (r • m) = σ r • τ m) :
    Module.Finite R M := by
  classical
  letI : DecidableEq M := Classical.decEq M
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R') (M := M')
  refine ⟨⟨s.image (fun y => τ.symm y), ?_⟩⟩
  have key : ∀ y ∈ Submodule.span R' (s : Set M'),
      τ.symm y ∈ Submodule.span R
        ((s.image (fun y => τ.symm y) : Finset M) : Set M) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        refine Submodule.subset_span ?_
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => simpa [map_add] using Submodule.add_mem _ ha hb
    | smul r' a _ ha =>
        rw [symm_smul σ τ hc]
        exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  rintro m -
  have hm : τ m ∈ Submodule.span R' (s : Set M') := by
    rw [hs]; trivial
  simpa using key (τ m) hm

end ProximityPrize.SubmissionLower.LocalMathlibSemilinearFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibSemilinearFinite.finite_of_semilinear_equiv
