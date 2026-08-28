/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneNoSeparableDegree

/-!
# Accumulating resultant multiplicity over a family

The family form of the planar bound needs the multiplicities contributed by
distinct components to ADD.  Two purely polynomial statements do that, with
no field extension in sight:

* `pow_sum_dvd_resultant` — distinct monic irreducible common factors of the
  two specialised polynomials over the residue field `AdjoinRoot f` are
  pairwise coprime, so their product is a common factor, and the resulting
  Sylvester corank makes `f` divide the resultant to the summed degree;
* `prod_pow_dvd_of_per_prime` — per-prime multiplicity bounds combine into
  one product, by peeling off a whole fibre at a time and using that
  distinct monic irreducibles are coprime.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.PlaneNoSeparableMultiplicity

open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

/-- **The summed degree of distinct common irreducible factors over the
residue field is a lower bound on the multiplicity of `f` in the
resultant.** -/
theorem pow_sum_dvd_resultant
    (P Q : Polynomial (Polynomial K)) (f : Polynomial K) [Fact (Irreducible f)]
    {J : Type} [Fintype J] [DecidableEq J]
    (G : J → Polynomial (AdjoinRoot f))
    (hmonic : ∀ j, (G j).Monic) (hirr : ∀ j, Irreducible (G j))
    (hGinj : Function.Injective G)
    (hdvdP : ∀ j, G j ∣ P.map (AdjoinRoot.mk f))
    (hdvdQ : ∀ j, G j ∣ Q.map (AdjoinRoot.mk f))
    (hPne : P.map (AdjoinRoot.mk f) ≠ 0) :
    f ^ (∑ j, (G j).natDegree) ∣
      Polynomial.resultant P Q P.natDegree Q.natDegree := by
  classical
  letI : DecidableEq (AdjoinRoot f) := Classical.decEq _
  letI : DecidableEq K := Classical.decEq _
  have hfirr : Irreducible f := Fact.out
  have hfprime : Prime f := hfirr.prime
  set H : Polynomial (AdjoinRoot f) := ∏ j, G j with hH
  have hcoprime : Pairwise (Function.onFun IsCoprime G) := by
    intro i j hij
    show IsCoprime (G i) (G j)
    refine (hirr i).coprime_iff_not_dvd.mpr ?_
    intro hdvd
    exact hij (hGinj (Polynomial.eq_of_monic_of_associated (hmonic i) (hmonic j)
      ((hirr i).associated_of_dvd (hirr j) hdvd)))
  have hHdvdP : H ∣ P.map (AdjoinRoot.mk f) :=
    Fintype.prod_dvd_of_coprime hcoprime hdvdP
  have hHdvdQ : H ∣ Q.map (AdjoinRoot.mk f) :=
    Fintype.prod_dvd_of_coprime hcoprime hdvdQ
  have hHmonic : H.Monic := Polynomial.monic_prod_of_monic _ _ (fun j _ => hmonic j)
  have hHne : H ≠ 0 := hHmonic.ne_zero
  have hHdeg : H.natDegree = ∑ j, (G j).natDegree :=
    Polynomial.natDegree_prod _ _ (fun j _ => (hmonic j).ne_zero)
  -- the summed degree fits under the fixed Sylvester caps
  have hHle : H.natDegree ≤ P.natDegree := by
    refine le_trans (Polynomial.natDegree_le_of_dvd hHdvdP hPne) ?_
    exact Polynomial.natDegree_map_le
  have hPdeg : (P.map (AdjoinRoot.mk f)).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_map_le
  have hQdeg : (Q.map (AdjoinRoot.mk f)).natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_map_le
  have hrank : (Polynomial.sylvester (P.map (AdjoinRoot.mk f))
      (Q.map (AdjoinRoot.mk f)) P.natDegree Q.natDegree).rank
        ≤ P.natDegree + Q.natDegree - H.natDegree :=
    PlaneNoSeparableDegree.sylvester_rank_le_of_common_divisor _ _ H
      P.natDegree Q.natDegree hPdeg hQdeg hHne hHdvdP hHdvdQ (by omega)
  have hmapsyl : (Polynomial.sylvester P Q P.natDegree Q.natDegree).map
      (AdjoinRoot.mk f)
      = Polynomial.sylvester (P.map (AdjoinRoot.mk f))
          (Q.map (AdjoinRoot.mk f)) P.natDegree Q.natDegree := by
    rw [Polynomial.sylvester_map_map]
    rfl
  have hcorank := LocalMathlibPrimeCorankDet.pow_corank_dvd_det_of_surjective
    (AdjoinRoot.mk f) (AdjoinRoot.mk_surjective) f hfprime
    (fun p => AdjoinRoot.mk_eq_zero) (Polynomial.sylvester P Q P.natDegree Q.natDegree)
  rw [hmapsyl, Fintype.card_fin] at hcorank
  have hdet : (Polynomial.sylvester P Q P.natDegree Q.natDegree).det
      = Polynomial.resultant P Q P.natDegree Q.natDegree := rfl
  rw [hdet] at hcorank
  rw [← hHdeg]
  exact dvd_trans (pow_dvd_pow f (by omega)) hcorank

/-- Per-prime multiplicity bounds combine into a single product. -/
theorem prod_pow_dvd_of_per_prime
    {I : Type} [DecidableEq I] [DecidableEq (Polynomial K)]
    (fi : I → Polynomial K) (n : I → ℕ) (R : Polynomial K)
    (hmonic : ∀ i, (fi i).Monic) (hirr : ∀ i, Irreducible (fi i)) :
    ∀ s : Finset I,
      (∀ f : Polynomial K,
        f ^ (∑ i ∈ s.filter (fun i => fi i = f), n i) ∣ R) →
      (∏ i ∈ s, fi i ^ n i) ∣ R := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hper
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
    · simp
    · set f : Polynomial K := fi i₀ with hf
      set t : Finset I := s.filter (fun i => ¬ (fi i = f)) with ht
      have htsub : t ⊂ s := by
        refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨i₀, hi₀, ?_⟩
        rw [Finset.mem_filter]
        rintro ⟨-, hcon⟩
        exact hcon hf.symm
      have hperT : ∀ g : Polynomial K,
          g ^ (∑ i ∈ t.filter (fun i => fi i = g), n i) ∣ R := by
        intro g
        refine dvd_trans (pow_dvd_pow g ?_) (hper g)
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        rw [ht, Finset.mem_filter] at hi
        exact ⟨hi.1.1, hi.2⟩
      have hIH : (∏ i ∈ t, fi i ^ n i) ∣ R := ih t htsub hperT
      have hsplit : (∏ i ∈ s, fi i ^ n i)
          = (∏ i ∈ s.filter (fun i => fi i = f), fi i ^ n i) *
            (∏ i ∈ t, fi i ^ n i) := by
        rw [ht]
        exact (Finset.prod_filter_mul_prod_filter_not s (fun i => fi i = f) _).symm
      have hpow : (∏ i ∈ s.filter (fun i => fi i = f), fi i ^ n i)
          = f ^ (∑ i ∈ s.filter (fun i => fi i = f), n i) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_congr rfl (fun i hi => ?_)
        rw [(Finset.mem_filter.mp hi).2]
      have hcop : IsCoprime (f ^ (∑ i ∈ s.filter (fun i => fi i = f), n i))
          (∏ i ∈ t, fi i ^ n i) := by
        refine IsCoprime.pow_left ?_
        refine IsCoprime.prod_right (fun i hi => ?_)
        refine IsCoprime.pow_right ?_
        refine (hirr i₀).coprime_iff_not_dvd.mpr ?_
        intro hdvd
        have hne : ¬ (fi i = f) := by
          rw [ht, Finset.mem_filter] at hi
          exact hi.2
        exact hne (Polynomial.eq_of_monic_of_associated (hmonic i) (hmonic i₀)
          (((hirr i₀).associated_of_dvd (hirr i) hdvd)).symm)
      rw [hsplit, hpow]
      exact hcop.mul_dvd (hper f) hIH

end

end ProximityPrize.SubmissionLower.PlaneNoSeparableMultiplicity

#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableMultiplicity.pow_sum_dvd_resultant
#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableMultiplicity.prod_pow_dvd_of_per_prime
