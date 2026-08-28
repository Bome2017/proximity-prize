/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# Determinant divisibility from corank at a prime residue field

`MatrixRootMultiplicity.pow_corank_dvd_det` proves that a rank loss of a
polynomial matrix at a SCALAR specialization forces the corresponding linear
factor to divide the determinant to that power.  The same argument works
verbatim at any prime whose residue ring is a field: the rank normal form is
taken over the residue field and lifted through an arbitrary set-theoretic
section of the quotient map, and the two change-of-basis determinants are
killed at the end by primality instead of by being units.

* `pow_card_dvd_det_of_columns_dvd`;
* `pow_corank_dvd_det_of_surjective`.

This removes the need for the residue field to be the base field, which is
what lets a bidegree bound be proved at the minimal polynomial of a
coordinate rather than only at rational points.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibPrimeCorankDet

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]
variable {L : Type*} [Field L] [DecidableEq L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whole columns divisible by `f` each contribute one factor of `f` to
every determinant permutation product. -/
theorem pow_card_dvd_det_of_columns_dvd
    (f : R) (M : Matrix ι ι R) (columns : Finset ι)
    (hzero : ∀ j ∈ columns, ∀ i, f ∣ M i j) :
    f ^ columns.card ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  have hpart : (∏ _j ∈ columns, f) ∣ ∏ j ∈ columns, M (permutation j) j := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact hzero j hj (permutation j)
  have hfull :
      (∏ j ∈ columns, M (permutation j) j) ∣ ∏ j : ι, M (permutation j) j :=
    Finset.prod_dvd_prod_of_subset columns Finset.univ
      (fun j => M (permutation j) j) (Finset.subset_univ columns)
  have hproduct : f ^ columns.card ∣ ∏ j : ι, M (permutation j) j := by
    simpa using hpart.trans hfull
  exact dvd_mul_of_dvd_right hproduct _

/-- **Corank at a prime bounds the multiplicity of that prime in the
determinant.**  No hypothesis relates `L` to `R` beyond `φ` being a
surjection with kernel `(f)`. -/
theorem pow_corank_dvd_det_of_surjective
    (φ : R →+* L) (hsurj : Function.Surjective φ)
    (f : R) (hf : Prime f) (hker : ∀ p : R, φ p = 0 ↔ f ∣ p)
    (M : Matrix ι ι R) :
    f ^ (Fintype.card ι - (M.map φ).rank) ∣ M.det := by
  classical
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form (M.map φ)
  let s : L → R := Function.surjInv hsurj
  have hs : ∀ x : L, φ (s x) = x := Function.surjInv_eq hsurj
  let V' : Matrix ι ι R := V.map s
  let U' : Matrix ι ι R := U.map s
  have hVmap : V'.map φ = V := by
    ext i j
    exact hs _
  have hUmap : U'.map φ = U := by
    ext i j
    exact hs _
  let T : Matrix ι ι R := V' * M * U'
  have hTmap : T.map φ = V * (M.map φ) * U := by
    have hring : φ.mapMatrix (V' * M * U') =
        φ.mapMatrix V' * φ.mapMatrix M * φ.mapMatrix U' := by
      rw [map_mul, map_mul]
    simpa only [RingHom.mapMatrix_apply, hVmap, hUmap] using hring
  let zeroEmbedding : Fin (Fintype.card ι - (M.map φ).rank) ↪ ι := {
    toFun := fun j => e.symm (Sum.inr j)
    inj' := by
      intro i j hij
      exact Sum.inr.inj (e.symm.injective hij) }
  let zeroColumns : Finset ι := Finset.univ.map zeroEmbedding
  have hcard : zeroColumns.card = Fintype.card ι - (M.map φ).rank := by
    simp [zeroColumns]
  have hzero : ∀ j ∈ zeroColumns, ∀ i, f ∣ T i j := by
    intro j hj i
    obtain ⟨j0, _, rfl⟩ := Finset.mem_map.mp hj
    refine (hker _).mp ?_
    show (T.map φ) i (e.symm (Sum.inr j0)) = 0
    rw [hTmap, hnormal]
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hdiv := pow_card_dvd_det_of_columns_dvd f T zeroColumns hzero
  rw [hcard] at hdiv
  have hdet : T.det = V'.det * M.det * U'.det := by
    simp only [T, Matrix.det_mul]
  have hVne : V.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hV).ne_zero
  have hUne : U.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero
  have hVdvd : ¬ f ∣ V'.det := by
    intro hcon
    apply hVne
    have hzeroV : φ V'.det = 0 := (hker _).mpr hcon
    rwa [RingHom.map_det, RingHom.mapMatrix_apply, hVmap] at hzeroV
  have hUdvd : ¬ f ∣ U'.det := by
    intro hcon
    apply hUne
    have hzeroU : φ U'.det = 0 := (hker _).mpr hcon
    rwa [RingHom.map_det, RingHom.mapMatrix_apply, hUmap] at hzeroU
  rw [hdet] at hdiv
  have hstep : f ^ (Fintype.card ι - (M.map φ).rank) ∣ M.det * U'.det := by
    refine hf.pow_dvd_of_dvd_mul_left _ hVdvd ?_
    rwa [mul_assoc] at hdiv
  exact hf.pow_dvd_of_dvd_mul_right _ hUdvd hstep

end

end ProximityPrize.SubmissionLower.LocalMathlibPrimeCorankDet

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPrimeCorankDet.pow_card_dvd_det_of_columns_dvd
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibPrimeCorankDet.pow_corank_dvd_det_of_surjective
