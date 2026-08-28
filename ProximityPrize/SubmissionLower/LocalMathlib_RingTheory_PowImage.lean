/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_ExpandEquiv

/-!
# `C ^ q` as an `A₀`-submodule, and the semilinear equivalence

Eighth unit: the `N` and `τ` that `finite_of_frobenius_descent` consumes.

Given a subring `A₀ ⊆ A` together with a ring isomorphism `σ : A ≃+* A₀`
realising the `q`-power map (which is `frobEquiv` at the intended instance),
and an `A`-subalgebra `C ⊆ L`, the set `C ^ q` is:

* an `A₀`-submodule of `L` — `powImage`.  Closed under addition by the
  freshman's dream, and under `A₀`-scalars because every `c : A₀` is `σ a`,
  so `c • x ^ q = (a • x) ^ q` with `a • x ∈ C`;
* additively isomorphic to `C` — `powEquiv`, since the `q`-power map is
  injective on a reduced ring;
* and the pair is semilinear over `σ` — `powEquiv_smul`.

Those are exactly the three inputs the descent needs on the module side.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibPowImage

set_option linter.unusedSectionVars false

variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]
variable (p e : ℕ) [ExpChar L p]
variable (A₀ : Subring A) (σ : A ≃+* A₀) (hσ : ∀ a : A, ((σ a : A)) = a ^ p ^ e)
variable (C : Subalgebra A L)

/-- `L` as an `A₀`-algebra, through `A₀ ⊆ A → L`. -/
@[reducible] noncomputable def algebraA₀ : Algebra A₀ L :=
  ((algebraMap A L).comp A₀.subtype).toAlgebra

attribute [local instance] algebraA₀

theorem algebraMap_A₀ (c : A₀) :
    (algebraMap A₀ L) c = algebraMap A L (c : A) := rfl

/-- **`C ^ q` is an `A₀`-submodule of `L`.** -/
def powImage : Submodule A₀ L where
  carrier := {y : L | ∃ x ∈ C, x ^ p ^ e = y}
  add_mem' := by
    rintro y z ⟨x, hx, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨x + w, C.add_mem hx hw, add_pow_expChar_pow x w p e⟩
  zero_mem' := by
    refine ⟨0, C.zero_mem, ?_⟩
    rw [zero_pow (pow_ne_zero e (expChar_ne_zero L p))]
  smul_mem' := by
    rintro c y ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := σ.surjective c
    refine ⟨a • x, C.smul_mem hx a, ?_⟩
    rw [Algebra.smul_def, mul_pow, ← map_pow, ← hσ, ← algebraMap_A₀ A₀ (σ a),
      ← Algebra.smul_def]

theorem mem_powImage_iff (y : L) :
    y ∈ powImage p e A₀ σ hσ C ↔ ∃ x ∈ C, x ^ p ^ e = y := Iff.rfl

/-- The `q`-power map as an additive homomorphism `C → C ^ q`. -/
noncomputable def powHom : C →+ powImage p e A₀ σ hσ C :=
  AddMonoidHom.mk' (fun x => ⟨(x : L) ^ p ^ e, ⟨(x : L), x.2, rfl⟩⟩)
    (fun x y => Subtype.ext (add_pow_expChar_pow (x : L) (y : L) p e))

theorem powHom_apply (x : C) : ((powHom p e A₀ σ hσ C x : L)) = (x : L) ^ p ^ e := rfl

/-- **The `q`-power map is an additive isomorphism `C ≃+ C ^ q`.** -/
noncomputable def powEquiv : C ≃+ powImage p e A₀ σ hσ C :=
  AddEquiv.ofBijective (powHom p e A₀ σ hσ C) (by
    constructor
    · intro x y hxy
      have h : (x : L) ^ p ^ e = (y : L) ^ p ^ e := congrArg Subtype.val hxy
      exact Subtype.ext (iterateFrobenius_inj L p e h)
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)

theorem powEquiv_apply (x : C) :
    ((powEquiv p e A₀ σ hσ C x : L)) = (x : L) ^ p ^ e := rfl

/-- **Semilinearity over `σ`.** -/
theorem powEquiv_smul (a : A) (x : C) :
    powEquiv p e A₀ σ hσ C (a • x) = σ a • powEquiv p e A₀ σ hσ C x := by
  apply Subtype.ext
  have hcoe : ((a • x : C) : L) = algebraMap A L a * (x : L) := by
    rw [Algebra.smul_def]; simp
  rw [powEquiv_apply, Submodule.coe_smul, powEquiv_apply, hcoe, mul_pow,
    Algebra.smul_def, algebraMap_A₀, hσ, map_pow]

end ProximityPrize.SubmissionLower.LocalMathlibPowImage

#print axioms ProximityPrize.SubmissionLower.LocalMathlibPowImage.powImage
#print axioms ProximityPrize.SubmissionLower.LocalMathlibPowImage.powEquiv
#print axioms ProximityPrize.SubmissionLower.LocalMathlibPowImage.powEquiv_smul
