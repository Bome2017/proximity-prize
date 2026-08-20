/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.BCHKS6317

/-!
# Explicit target-radius decode witnesses

An `IsMCA` event is stated using projected code membership on an arbitrary sufficiently large
set.  The algebraic proof needs an actual polynomial and one fixed integral agreement size.
This file performs that conversion locally and without strengthening the event.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped BigOperators ENNReal NNReal

section ExactSupport

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- If a word is not an RS word on `S₀`, a prescribed-size subset can retain that failure.
The proof interpolates on `k` nodes and keeps one node witnessing failure. -/
lemma exists_bad_subset_card_eq_6317 {domain : ι ↪ F} {k a : ℕ}
    (hk : 0 < k) (hka : k + 1 ≤ a) {S₀ : Finset ι} (haS : a ≤ S₀.card)
    (u : ι → F)
    (hu : LinearCode.projectedWord u S₀ ∉
      LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S₀) :
    ∃ S : Finset ι, S ⊆ S₀ ∧ S.card = a ∧
      LinearCode.projectedWord u S ∉
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain k) S := by
  classical
  obtain ⟨K, hKS₀, hKcard⟩ :=
    Finset.exists_subset_card_eq (s := S₀) (n := k) (by omega)
  let q : Polynomial F := Lagrange.interpolate K domain u
  have hqdeg : q.natDegree < k := by
    by_cases hq : q = 0
    · simp [hq, hk]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hq, ← hKcard]
      exact Lagrange.degree_interpolate_lt u domain.injective.injOn
  have hqdegree : q.degree < k := by
    by_cases hq : q = 0
    · simp [hq]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hq).mp hqdeg
  have hqmem : ReedSolomon.evalOnPoints domain q ∈ ReedSolomon.code domain k :=
    ReedSolomon.evalOnPoints_mem_code_of_degree_lt hqdegree
  have hx : ∃ x ∈ S₀, q.eval (domain x) ≠ u x := by
    by_contra h
    push Not at h
    apply hu
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨ReedSolomon.evalOnPoints domain q, hqmem, ?_⟩
    funext i
    simp only [LinearCode.projectedWord, Set.restrict_apply, ReedSolomon.evalOnPoints]
    exact (h i.1 i.2).symm
  obtain ⟨x, hxS₀, hxneq⟩ := hx
  have hxK : x ∉ K := by
    intro hxK
    exact hxneq (Lagrange.eval_interpolate_at_node u domain.injective.injOn hxK)
  have hinsert_sub : insert x K ⊆ S₀ := Finset.insert_subset hxS₀ hKS₀
  have hinsert_card : (insert x K).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hxK, hKcard]
  obtain ⟨S, hsubS, hSS₀, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hinsert_sub (by omega) haS
  refine ⟨S, hSS₀, hScard, ?_⟩
  intro huS
  rw [LinearCode.mem_projectedCodeSubmod_iff] at huS
  obtain ⟨c, hc, hcu⟩ := huS
  change c ∈ ReedSolomon.code domain k at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨p, hpdegree, rfl⟩ := hc
  have hpdeg : p.natDegree < k := by
    by_cases hp : p = 0
    · simp [hp, hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hpdegree
  have hpq : p = q := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
      (f := fun i : ↥K => domain i.1) ?_ ?_ ?_
    · intro i j hij
      exact Subtype.ext (domain.injective hij)
    · intro i
      have hiS : i.1 ∈ S := hsubS (Finset.mem_insert_of_mem i.2)
      have hcui := congrFun hcu ⟨i.1, hiS⟩
      simpa [q, LinearCode.projectedWord, ReedSolomon.evalOnPoints] using
        hcui.symm.trans
          (Lagrange.eval_interpolate_at_node u domain.injective.injOn i.2).symm
    · rw [Fintype.card_coe, hKcard]
      exact max_lt hpdeg hqdeg
  have hxS : x ∈ S := hsubS (Finset.mem_insert_self x K)
  have hcx := congrFun hcu ⟨x, hxS⟩
  apply hxneq
  simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints, hpq] using hcx.symm

/-- An explicit polynomial decode attached to one target MCA scalar. -/
structure TargetDecode
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (γ : IRSProfile.Field) where
  support : Finset IRSProfile.Index
  polynomial : Polynomial IRSProfile.Field
  support_card : support.card = 186199
  degree_lt : polynomial.degree < IRSProfile.baseDimension
  agreement : ∀ i ∈ support,
    polynomial.eval (IRSProfile.domain i) = U 0 i + γ * U 1 i
  row_failure : ∃ j : Fin 2,
    LinearCode.projectedWord (U j) support ∉
      LinearCode.projectedCodeSubmod IRSProfile.baseCode support

/-- The target real-radius inequality rounds up to exactly 186,199 agreement positions. -/
lemma target_agreement_card_le {S : Finset IRSProfile.Index}
    (hS : (S.card : ℝ) ≥
      (Fintype.card IRSProfile.Index : ℝ) * (1 - (targetRadius : ℝ))) :
    186199 ≤ S.card := by
  have hstrict : (186198 : ℝ) < (S.card : ℝ) := by
    norm_num [targetRadius, IRSProfile.Index] at hS ⊢
    linarith
  exact_mod_cast hstrict

/-- Every target MCA event produces the exact explicit decode data used downstream. -/
theorem exists_targetDecode
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) (γ : IRSProfile.Field)
    (hγ : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode γ U
      (targetRadius : ℝ)) :
    Nonempty (TargetDecode U γ) := by
  classical
  obtain ⟨S₀, hS₀, hcomb, j, hj⟩ := hγ
  obtain ⟨S, hSS₀, hScard, hjS⟩ :=
    exists_bad_subset_card_eq_6317
      (domain := IRSProfile.domain) (k := IRSProfile.baseDimension)
      (a := 186199) (by norm_num [IRSProfile.baseDimension])
      (by norm_num [IRSProfile.baseDimension]) (target_agreement_card_le hS₀)
      (U j) hj
  have hcombS :
      LinearCode.projectedWord
          (fun x => ∑ r, AffineLineGenerator IRSProfile.Field γ r • U r x) S ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode S := by
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb ⊢
    obtain ⟨c, hc, hceq⟩ := hcomb
    refine ⟨c, hc, ?_⟩
    funext i
    exact congrFun hceq ⟨i.1, hSS₀ i.2⟩
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcombS
  obtain ⟨c, hc, hceq⟩ := hcombS
  change c ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨P, hPdeg, rfl⟩ := hc
  refine ⟨{
    support := S
    polynomial := P
    support_card := hScard
    degree_lt := hPdeg
    agreement := ?_
    row_failure := ⟨j, hjS⟩ }⟩
  intro i hi
  have heq := congrFun hceq ⟨i, hi⟩
  simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints,
    AffineLineGenerator, Fin.sum_univ_two] using heq.symm

end ExactSupport

end ProximityPrize.SubmissionLower
