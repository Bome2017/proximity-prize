/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# `K[X]` is a finite module over `K[X ^ q]`

First unit of the separability-free finiteness chain.

`LocalMathlib_RingTheory_DedekindDomain_NoSeparable` reduces the whole
mixed-bidegree gate to a single obligation: `Module.Finite A C` for the
integral closure `C`, in the possibly-inseparable case.  Over a perfect base
field that is true, by the classical purely-inseparable base change: take
`q = p ^ e` killing the inseparable exponent, pass to `F' = F ^ (1/q)`, where
the extension becomes separable, apply the separable case there, and descend
because the closure in `L` is a submodule of a finite module over a
Noetherian ring.

The base change is realised concretely by `Polynomial.expand K q`, which
presents `K[X]` as `K[X ^ q]`-algebra — and `K(X) ^ q ⊆ K(X ^ q)` exactly
when `K` is perfect, since `(∑ aᵢ Xⁱ) ^ q = ∑ aᵢ ^ q X ^ (i q)`.

This file supplies the module-theoretic step of that base change, which is
characteristic-free and needs no perfectness:

* `span_range_X_pow_eq_top` — `{X ^ i}_{i < q}` spans `K[X]` over `K[X ^ q]`;
* `finite_over_expand` — hence `K[X]` is a finite `K[X ^ q]`-module.

Neither statement is in Mathlib (checked: no `Module.Free`/`Basis` result for
`Polynomial.expand`, and no Japanese/N-2 theory at all).

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibExpandFinite

open Polynomial

-- NOTE: `Polynomial.Bivariate`'s scoped notation rebinds bare `X` to `C X`,
-- so every occurrence below is fully qualified.

variable (K : Type*) [CommRing K] (q : ℕ)

/-- The subring `K[X ^ q] ⊆ K[X]`, presented as the range of `expand K q`. -/
noncomputable def expandRange : Subring (Polynomial K) :=
  (Polynomial.expand K q).toRingHom.range

noncomputable instance : Algebra (expandRange K q) (Polynomial K) :=
  (expandRange K q).subtype.toAlgebra

theorem X_pow_mul_mem (a : ℕ) :
    (Polynomial.X : Polynomial K) ^ (q * a) ∈ expandRange K q := by
  refine ⟨(Polynomial.X : Polynomial K) ^ a, ?_⟩
  show Polynomial.expand K q ((Polynomial.X : Polynomial K) ^ a) = _
  rw [map_pow, Polynomial.expand_X, ← pow_mul]

theorem C_mem_expandRange (c : K) :
    (Polynomial.C c : Polynomial K) ∈ expandRange K q := by
  refine ⟨(Polynomial.C c : Polynomial K), ?_⟩
  show Polynomial.expand K q (Polynomial.C c) = _
  rw [Polynomial.expand_C]

/-- **The spanning set.**  Every polynomial is a `K[X ^ q]`-combination of
`1, X, …, X ^ (q - 1)`: split each exponent as `n = q * a + i`. -/
theorem span_range_X_pow_eq_top (hq : 0 < q) :
    Submodule.span (expandRange K q)
        (Set.range fun i : Fin q => (Polynomial.X : Polynomial K) ^ (i : ℕ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro f -
  induction f using Polynomial.induction_on' with
  | add p r hp hr => exact Submodule.add_mem _ hp hr
  | monomial n c =>
      have hsplit : q * (n / q) + n % q = n := Nat.div_add_mod n q
      have hlt : n % q < q := Nat.mod_lt _ hq
      have hbase : (Polynomial.C c * Polynomial.X ^ (q * (n / q)) : Polynomial K)
          ∈ expandRange K q :=
        Subring.mul_mem _ (C_mem_expandRange K q c) (X_pow_mul_mem K q _)
      have hmem : (Polynomial.X : Polynomial K) ^ (n % q) ∈
          Submodule.span (expandRange K q)
            (Set.range fun i : Fin q => (Polynomial.X : Polynomial K) ^ (i : ℕ)) :=
        Submodule.subset_span ⟨⟨n % q, hlt⟩, rfl⟩
      have hEq : (Polynomial.monomial n c : Polynomial K) =
          (⟨Polynomial.C c * Polynomial.X ^ (q * (n / q)), hbase⟩ : expandRange K q) •
            ((Polynomial.X : Polynomial K) ^ (n % q)) := by
        rw [Algebra.smul_def]
        show (Polynomial.monomial n c : Polynomial K) =
          (Polynomial.C c * Polynomial.X ^ (q * (n / q))) * Polynomial.X ^ (n % q)
        rw [mul_assoc, ← pow_add, hsplit, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hEq]
      exact Submodule.smul_mem _ _ hmem

/-- **`K[X]` is a finite `K[X ^ q]`-module.** -/
theorem finite_over_expand (hq : 0 < q) :
    Module.Finite (expandRange K q) (Polynomial K) := by
  classical
  refine ⟨⟨(Finset.univ : Finset (Fin q)).image
    (fun i : Fin q => (Polynomial.X : Polynomial K) ^ (i : ℕ)), ?_⟩⟩
  have hcoe : (↑((Finset.univ : Finset (Fin q)).image
      (fun i : Fin q => (Polynomial.X : Polynomial K) ^ (i : ℕ))) : Set (Polynomial K))
      = Set.range fun i : Fin q => (Polynomial.X : Polynomial K) ^ (i : ℕ) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hcoe]
  exact span_range_X_pow_eq_top K q hq

end ProximityPrize.SubmissionLower.LocalMathlibExpandFinite

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandFinite.span_range_X_pow_eq_top
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandFinite.finite_over_expand
