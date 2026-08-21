import ProximityPrize.SubmissionLower.FiniteTaylorCore

/-!
# Fixed-resultant rigidity and asymmetric height bounds

This file contains only the resultant argument needed by the 53.14 assembly.
It is independent of the finite Taylor recursion.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorResultantRigidity

open Polynomial Matrix
open FiniteTaylorCore

noncomputable section

variable {F : Type*} [Field F]

def specializeZ (z : F) (P : Polynomial (Polynomial F)) : Polynomial F :=
  P.map (Polynomial.evalRingHom z)

def evalZT (z y : F) : Polynomial (Polynomial F) →+* F :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y

/-- The fixed-size resultant chosen before specialization. -/
def quotientResultant (H beta : Polynomial (Polynomial F)) : Polynomial F :=
  Polynomial.resultant H beta H.natDegree beta.natDegree

theorem polynomial_eq_zero_of_many_evaluations
    {Seed : Type*} [DecidableEq Seed]
    (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (P : Polynomial F) (hcard : P.natDegree < seeds.card)
    (hvanish : ∀ seed ∈ seeds, P.eval (z seed) = 0) :
    P = 0 := by
  classical
  by_contra hP
  have himage : (seeds.image z).card = seeds.card :=
    Finset.card_image_iff.mpr hz
  have hroots : (seeds.image z).val ⊆ P.roots := by
    intro root hroot
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp
      (show root ∈ seeds.image z from hroot)
    exact (Polynomial.mem_roots hP).mpr (hvanish seed hseed)
  have hle : seeds.card ≤ P.natDegree := by
    rw [← himage]
    exact Polynomial.card_le_degree_of_subset_roots hroots
  omega

theorem quotientResultant_eval_eq_zero_of_common_root
    (H beta : Polynomial (Polynomial F)) (hHpos : 0 < H.natDegree)
    (z y : F) (hHroot : (specializeZ z H).eval y = 0)
    (hbetaRoot : (specializeZ z beta).eval y = 0) :
    (quotientResultant H beta).eval z = 0 := by
  let f := specializeZ z H
  let g := specializeZ z beta
  have hfdeg : f.natDegree ≤ H.natDegree := Polynomial.natDegree_map_le
  have hgdeg : g.natDegree ≤ beta.natDegree := Polynomial.natDegree_map_le
  obtain ⟨p, q, _hp, _hq, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hfdeg hgdeg
      (Or.inl hHpos.ne')
  have heval := congrArg (Polynomial.evalRingHom y) hbez
  have hfixed :
      Polynomial.resultant f g H.natDegree beta.natDegree = 0 := by
    simpa [f, g, hHroot, hbetaRoot] using heval.symm
  change (Polynomial.evalRingHom z)
    (Polynomial.resultant H beta H.natDegree beta.natDegree) = 0
  rw [← Polynomial.resultant_map_map]
  exact hfixed

theorem beta_eq_zero_of_quotientResultant_eq_zero
    (H beta : Polynomial (Polynomial F))
    (hHirr : Irreducible
      (H.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))))
    (hHpos : 0 < H.natDegree)
    (hbetaDegree : beta.natDegree < H.natDegree)
    (hresultant : quotientResultant H beta = 0) :
    beta = 0 := by
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  let f : Polynomial K := H.map φ
  let g : Polynomial K := beta.map φ
  have hφinj : Function.Injective φ :=
    IsFractionRing.injective (Polynomial F) K
  have hfirr : Irreducible f := by
    simpa [f, K, φ] using hHirr
  have hfdeg : f.natDegree = H.natDegree :=
    by simpa [f] using Polynomial.natDegree_map_eq_of_injective hφinj H
  have hgdeg : g.natDegree = beta.natDegree :=
    by simpa [g] using Polynomial.natDegree_map_eq_of_injective hφinj beta
  have hresK : Polynomial.resultant f g = 0 := by
    change Polynomial.resultant f g f.natDegree g.natDegree = 0
    rw [hfdeg, hgdeg]
    dsimp only [f, g]
    rw [Polynomial.resultant_map_map H beta H.natDegree beta.natDegree φ]
    change φ (quotientResultant H beta) = 0
    rw [hresultant, map_zero]
  have hnotcop : ¬ IsCoprime f g :=
    (Polynomial.resultant_eq_zero_iff.mp hresK).2
  have hfg : f ∣ g := hfirr.dvd_iff_not_isCoprime.mpr hnotcop
  by_contra hbeta
  have hg0 : g ≠ 0 := by
    intro hg
    apply hbeta
    exact (Polynomial.map_injective φ hφinj) (by simpa [g] using hg)
  have hle : f.natDegree ≤ g.natDegree :=
    Polynomial.natDegree_le_of_dvd hfg hg0
  rw [hfdeg, hgdeg] at hle
  omega

theorem beta_eq_zero_of_many_common_roots
    {Seed : Type*} [DecidableEq Seed]
    (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (H beta : Polynomial (Polynomial F))
    (hHirr : Irreducible
      (H.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))))
    (hHpos : 0 < H.natDegree)
    (hbetaDegree : beta.natDegree < H.natDegree)
    (hresultantDegree : (quotientResultant H beta).natDegree < seeds.card)
    (yAt : Seed → F)
    (hHroot : ∀ seed ∈ seeds,
      (specializeZ (z seed) H).eval (yAt seed) = 0)
    (hbetaRoot : ∀ seed ∈ seeds,
      (specializeZ (z seed) beta).eval (yAt seed) = 0) :
    beta = 0 := by
  apply beta_eq_zero_of_quotientResultant_eq_zero H beta hHirr hHpos
    hbetaDegree
  apply polynomial_eq_zero_of_many_evaluations seeds z hz
    (quotientResultant H beta) hresultantDegree
  intro seed hseed
  exact quotientResultant_eval_eq_zero_of_common_root H beta hHpos
    (z seed) (yAt seed) (hHroot seed hseed) (hbetaRoot seed hseed)

/-! ## Asymmetric height bound -/

theorem natDegree_resultant_le_asymmetric
    (f g : Polynomial (Polynomial F)) (m n Df Dg : Nat)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (Polynomial.resultant f g m n).natDegree ≤ m * Dg + n * Df := by
  classical
  unfold Polynomial.resultant
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) •
        (∏ i, Polynomial.sylvester f g m n (σ i) i)).natDegree ≤
      (∏ i, Polynomial.sylvester f g m n (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  refine hsign.trans ((Polynomial.natDegree_prod_le
    (s := (Finset.univ : Finset (Fin (m + n))))
    (f := fun i => Polynomial.sylvester f g m n (σ i) i)).trans ?_)
  rw [Fin.sum_univ_add]
  apply Nat.add_le_add
  · calc
      ∑ i : Fin m,
          (Polynomial.sylvester f g m n (σ (Fin.castAdd n i))
            (Fin.castAdd n i)).natDegree ≤
          ∑ _i : Fin m, Dg := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [Polynomial.sylvester, Matrix.of_apply,
              Fin.addCases_left]
            split_ifs
            · exact hg _
            · simp
      _ = m * Dg := by simp
  · calc
      ∑ i : Fin n,
          (Polynomial.sylvester f g m n (σ (Fin.natAdd m i))
            (Fin.natAdd m i)).natDegree ≤
          ∑ _i : Fin n, Df := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [Polynomial.sylvester, Matrix.of_apply,
              Fin.addCases_right]
            split_ifs
            · exact hf _
            · simp
      _ = n * Df := by simp

theorem quotientResultant_natDegree_lt_2pow47
    (H beta : Polynomial (Polynomial F))
    (hHdeg : H.natDegree ≤ 11)
    (hbetaDeg : beta.natDegree ≤ 11)
    (hHheight : ∀ i, (H.coeff i).natDegree ≤ 792)
    (hbetaHeight : ∀ i, (beta.coeff i).natDegree ≤ 10104857200000) :
    (quotientResultant H beta).natDegree < 2 ^ 47 := by
  apply (natDegree_resultant_le_asymmetric H beta H.natDegree
    beta.natDegree 792 10104857200000 hHheight hbetaHeight).trans_lt
  have hm : H.natDegree * 10104857200000 ≤ 11 * 10104857200000 :=
    Nat.mul_le_mul_right _ hHdeg
  have hn : beta.natDegree * 792 ≤ 11 * 792 :=
    Nat.mul_le_mul_right _ hbetaDeg
  omega

end

end ProximityPrize.SubmissionLower.FiniteTaylorResultantRigidity
