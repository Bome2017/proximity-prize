/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower

/-!
# First post-quarter finite cell

This file contains the axiom-clean parts of the first score-improving cell:
the exact radius arithmetic, the four-codeword list bound, and the reduction
of the interleaved MCA term to the scalar Reed--Solomon code.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

noncomputable abbrev SquaredCode65541 : Set (IRSProfile.Index →
    Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

noncomputable abbrev delta65541 : ℝ≥0 :=
  (65541 : ℝ≥0) / 262144

noncomputable abbrev improvedRadius : ℝ≥0 :=
  (2731 : ℝ≥0) / 10923

theorem five_finset_overlap {α : Type*} [Fintype α] [DecidableEq α]
    (E0 E1 E2 E3 E4 : Finset α) :
    E0.card + E1.card + E2.card + E3.card + E4.card ≤
      Fintype.card α +
        ((E0 ∩ E1).card + (E0 ∩ E2).card + (E0 ∩ E3).card + (E0 ∩ E4).card +
         (E1 ∩ E2).card + (E1 ∩ E3).card + (E1 ∩ E4).card +
         (E2 ∩ E3).card + (E2 ∩ E4).card + (E3 ∩ E4).card) := by
  have h01 := Finset.card_union_add_card_inter E0 E1
  have h012 := Finset.card_union_add_card_inter (E0 ∪ E1) E2
  have h0123 := Finset.card_union_add_card_inter (E0 ∪ E1 ∪ E2) E3
  have h01234 := Finset.card_union_add_card_inter (E0 ∪ E1 ∪ E2 ∪ E3) E4
  have hdup2 : ((E0 ∪ E1) ∩ E2).card ≤
      (E0 ∩ E2).card + (E1 ∩ E2).card := by
    calc
      ((E0 ∪ E1) ∩ E2).card =
          ((E0 ∩ E2) ∪ (E1 ∩ E2)).card := by
            congr 1
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            tauto
      _ ≤ _ := Finset.card_union_le _ _
  have hdup3 : ((E0 ∪ E1 ∪ E2) ∩ E3).card ≤
      (E0 ∩ E3).card + (E1 ∩ E3).card + (E2 ∩ E3).card := by
    calc
      ((E0 ∪ E1 ∪ E2) ∩ E3).card =
          (((E0 ∩ E3) ∪ (E1 ∩ E3)) ∪ (E2 ∩ E3)).card := by
            congr 1
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            tauto
      _ ≤ ((E0 ∩ E3) ∪ (E1 ∩ E3)).card + (E2 ∩ E3).card :=
        Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hdup4 : ((E0 ∪ E1 ∪ E2 ∪ E3) ∩ E4).card ≤
      (E0 ∩ E4).card + (E1 ∩ E4).card + (E2 ∩ E4).card + (E3 ∩ E4).card := by
    calc
      ((E0 ∪ E1 ∪ E2 ∪ E3) ∩ E4).card =
          ((((E0 ∩ E4) ∪ (E1 ∩ E4)) ∪ (E2 ∩ E4)) ∪ (E3 ∩ E4)).card := by
            congr 1
            ext x
            simp only [Finset.mem_inter, Finset.mem_union]
            tauto
      _ ≤ (((E0 ∩ E4) ∪ (E1 ∩ E4)) ∪ (E2 ∩ E4)).card + (E3 ∩ E4).card :=
        Finset.card_union_le _ _
      _ ≤ ((E0 ∩ E4) ∪ (E1 ∩ E4)).card + (E2 ∩ E4).card + (E3 ∩ E4).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := by
        have hbase := Finset.card_union_le (E0 ∩ E4) (E1 ∩ E4)
        omega
  have hall : (E0 ∪ E1 ∪ E2 ∪ E3 ∪ E4).card ≤ Fintype.card α :=
    Finset.card_le_univ _
  omega

theorem no_five_close {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (C : Set (ι → α)) (hmin : Code.minDist C = 131073)
    (y : ι → α) (c : Fin 5 → ι → α)
    (hc : ∀ i, c i ∈ C) (hinj : Function.Injective c)
    (hr : ∀ i, Δ₀(y, c i) ≤ 65541)
    (hn : Fintype.card ι = 262144) : False := by
  let E : Fin 5 → Finset ι := fun i => Code.disagreementCols y (c i)
  have hE (i) : (E i).card ≤ 65541 := by
    simpa [E, ← Code.hammingDist_eq_disagreementCols_card] using hr i
  have hpair (i j : Fin 5) (hij : i ≠ j) :
      131073 + (E i ∩ E j).card ≤ (E i).card + (E j).card := by
    have hmd := Code.minDist_le_dist (hc i) (hc j) (hinj.ne hij)
    rw [hmin] at hmd
    have hsub : Code.disagreementCols (c i) (c j) ⊆ E i ∪ E j := by
      intro x hx
      simp only [E, Finset.mem_union, Code.mem_disagreementCols] at hx ⊢
      by_contra h
      push Not at h
      exact hx (h.1.symm.trans h.2)
    have hcard := Finset.card_le_card hsub
    have hu := Finset.card_union_add_card_inter (E i) (E j)
    rw [← Code.hammingDist_eq_disagreementCols_card] at hcard
    omega
  have h01 := hpair 0 1 (by decide)
  have h02 := hpair 0 2 (by decide)
  have h03 := hpair 0 3 (by decide)
  have h04 := hpair 0 4 (by decide)
  have h12 := hpair 1 2 (by decide)
  have h13 := hpair 1 3 (by decide)
  have h14 := hpair 1 4 (by decide)
  have h23 := hpair 2 3 (by decide)
  have h24 := hpair 2 4 (by decide)
  have h34 := hpair 3 4 (by decide)
  have hov := five_finset_overlap (E 0) (E 1) (E 2) (E 3) (E 4)
  have he0 := hE 0
  have he1 := hE 1
  have he2 := hE 2
  have he3 := hE 3
  have he4 := hE 4
  omega

theorem lambda_grid_le_four {α : Type*} [DecidableEq α]
    (C : Set (IRSProfile.Index → α)) (hmin : Code.minDist C = 131073) :
    Code.Lambda C
      (ProximityGap.gridPt (ι := IRSProfile.Index) 65541 : ℝ) ≤ 4 := by
  apply Code.Lambda_le_of_forall_finset_card_le
  intro y T hT
  apply Nat.le_of_lt_succ
  by_contra hnot
  have hfive : 5 ≤ T.card := Nat.le_of_not_gt hnot
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hfive
  let enum : Fin 5 ≃ S :=
    (finCongr hScard.symm).trans (Finset.equivFin S).symm
  let c : Fin 5 → IRSProfile.Index → α := fun i => (enum i).1
  have cinj : Function.Injective c := by
    intro i j hij
    apply enum.injective
    exact Subtype.ext hij
  have hclose (i : Fin 5) :
      c i ∈ Code.closeCodewordsRel C y
        (ProximityGap.gridPt (ι := IRSProfile.Index) 65541 : ℝ) := by
    apply hT
    exact hST (enum i).property
  have hc (i : Fin 5) : c i ∈ C :=
    (Code.mem_closeCodewordsRel_iff.mp (hclose i)).1
  have hr (i : Fin 5) : Δ₀(y, c i) ≤ 65541 := by
    have hrel := (Code.mem_closeCodewordsRel_iff.mp (hclose i)).2
    have hrelNN : ((δᵣ(y, c i) : ℚ≥0) : NNReal) ≤
        ProximityGap.gridPt (ι := IRSProfile.Index) 65541 := by
      exact_mod_cast hrel
    rw [Code.pairRelDist_le_iff_pairDist_le
      (ProximityGap.gridPt (ι := IRSProfile.Index) 65541)] at hrelNN
    rw [ProximityGap.gridPt_mul_card, Nat.floor_natCast] at hrelNN
    exact hrelNN
  exact no_five_close C hmin y c hc cinj hr (by norm_num [IRSProfile.Index])

theorem squaredCode65541_minDistance :
    Code.minDist SquaredCode65541 = 131073 := by
  calc
    Code.minDist SquaredCode65541 =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

theorem squaredCode_lambda_grid_65541_le_four :
    Code.Lambda SquaredCode65541
      (ProximityGap.gridPt (ι := IRSProfile.Index) 65541 : ℝ) ≤ 4 :=
  lambda_grid_le_four SquaredCode65541 squaredCode65541_minDistance

theorem improvedRadius_floor :
    ⌊improvedRadius * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = 65541 := by
  norm_num [improvedRadius, IRSProfile.Index]

theorem grid65541_floor :
    ⌊delta65541 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = 65541 := by
  norm_num [delta65541, IRSProfile.Index]

theorem squaredCode_lambda_improvedRadius_le_four :
    Code.Lambda SquaredCode65541 (improvedRadius : ℝ) ≤ 4 := by
  rw [ProximityGap.GrandChallenges.lambda_eq_of_floor_eq
    (C := SquaredCode65541) (δ := improvedRadius) (δ' := delta65541)
    (improvedRadius_floor.trans grid65541_floor.symm)]
  simpa [delta65541, ProximityGap.gridPt, IRSProfile.Index] using
    squaredCode_lambda_grid_65541_le_four

theorem mca_delta65541_eq_base :
    mcaError (AffineLineGenerator IRSProfile.Field)
      IRSProfile.code (delta65541 : ℝ) =
    mcaError (AffineLineGenerator IRSProfile.Field)
      IRSProfile.baseCode (delta65541 : ℝ) := by
  simpa [IRSProfile.code, IRSProfile.baseCode,
    ReedSolomon.Interleaved.irsCode,
    IRSProfile.totalDimension_div_interleaving] using
    (ProximityGap.mcaError_interleaved_eq
      IRSProfile.baseCode IRSProfile.interleaving delta65541
      (by norm_num [IRSProfile.interleaving])
      (by norm_num [delta65541])
      (by norm_num [delta65541]))

theorem certifiedGammaError_improvedRadius_le_of_base_mca
    (hmca :
      mcaError (AffineLineGenerator IRSProfile.Field)
          IRSProfile.baseCode (delta65541 : ℝ) ≤
        (2 : ENNReal) ^ (57 : ℕ) /
          (Fintype.card IRSProfile.Field : ENNReal)) :
    certifiedGammaError IRSProfile.code improvedRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  have hfloor :
      ⌊(improvedRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
        ⌊(delta65541 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ := by
    norm_num [improvedRadius, delta65541, IRSProfile.Index]
  have hmcaCode :
      mcaError (AffineLineGenerator IRSProfile.Field)
          IRSProfile.code (improvedRadius : ℝ) ≤
        (2 : ENNReal) ^ (57 : ℕ) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
    rw [CoreDefinitions.mcaError_eq_of_floor_eq
      (AffineLineGenerator IRSProfile.Field) IRSProfile.code
      (by positivity) (by positivity) hfloor]
    rw [mca_delta65541_eq_base]
    exact hmca
  have hLambdaNat :
      (Code.Lambda SquaredCode65541 (improvedRadius : ℝ)).toNat ≤ 4 :=
    ENat.toNat_le_of_le_coe squaredCode_lambda_improvedRadius_le_four
  have hList :
      ((Code.Lambda SquaredCode65541 (improvedRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (improvedRadius : ℝ) +
        ((Code.Lambda SquaredCode65541 (improvedRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
      (2 : ENNReal) ^ (57 : ℕ) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (4 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add hmcaCode hList
    _ ≤ (((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0) : ENNReal) := by
      have hne :
          (2 : ENNReal) ^ (57 : ℕ) /
                (Fintype.card IRSProfile.Field : ENNReal) +
              4 / (Fintype.card IRSProfile.Field : ENNReal) ≠ ⊤ := by
        rw [ENNReal.add_ne_top]
        constructor <;> apply ENNReal.div_ne_top <;> simp
      apply (ENNReal.toReal_le_toReal hne (by simp)).mp
      have hparts := ENNReal.add_ne_top.mp hne
      rw [ENNReal.toReal_add hparts.1 hparts.2,
        ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num [IRSProfile.Field, KoalaBear.Ext6]

theorem two_rpow_eighty_seven_div_one_hundred_ge :
    (2 : ℝ≥0) ^ (54 : ℕ) *
        ((8192 : ℝ≥0) / 10923) ^ (128 : ℕ) ≤
      (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
  have hrat :
      (2 : ℝ≥0) ^ (54 : ℕ) *
          ((8192 : ℝ≥0) / 10923) ^ (128 : ℕ) ≤
        (1871 : ℝ≥0) / 1024 := by
    have hnat :
        (2 : ℕ) ^ (1728 : ℕ) ≤
          1871 * (10923 : ℕ) ^ (128 : ℕ) := by
      set_option maxRecDepth 10000 in
        norm_num [pow_succ]
    have hmain :
        (2 : ℝ≥0) ^ (1728 : ℕ) ≤
          1871 * (10923 : ℝ≥0) ^ (128 : ℕ) := by
      exact_mod_cast hnat
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      (2 : ℝ≥0) ^ (54 : ℕ) * (8192 : ℝ≥0) ^ (128 : ℕ) * 1024 =
          (2 : ℝ≥0) ^ (1728 : ℕ) := by
        rw [show (8192 : ℝ≥0) = (2 : ℝ≥0) ^ (13 : ℕ) by norm_num,
          ← pow_mul,
          show (1024 : ℝ≥0) = (2 : ℝ≥0) ^ (10 : ℕ) by norm_num,
          ← pow_add, ← pow_add]
      _ ≤ 1871 * (10923 : ℝ≥0) ^ (128 : ℕ) := hmain
  have hroot :
      (1871 : ℝ≥0) / 1024 ≤
        ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (2 : ℝ≥0) ^ (54 : ℕ) *
        ((8192 : ℝ≥0) / 10923) ^ (128 : ℕ) ≤
      (1871 : ℝ≥0) / 1024 := hrat
    _ ≤ ((2 : ℝ≥0) ^ (87 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

theorem improvedRadius_admissible :
    claimedRadius 2731 10923 ∈
      Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [claimedRadius, IRSProfile.minRelativeDistance, div_lt_iff₀]

theorem improvedRadius_score_5313 :
    (1 - claimedRadius 2731 10923) ^ IRSProfile.repetitions ≤
      claimedError 5313 := by
  have hscaled :
      (2 : ℝ≥0) ^ (54 : ℕ) *
          (1 - claimedRadius 2731 10923) ^ IRSProfile.repetitions ≤
        (2 : ℝ≥0) ^ ((87 : ℝ) / 100) := by
    have hr :
        1 - claimedRadius 2731 10923 = (8192 : ℝ≥0) / 10923 := by
      change 1 - improvedRadius = (8192 : ℝ≥0) / 10923
      have hle : improvedRadius ≤ (1 : ℝ≥0) := by
        change (2731 : ℝ≥0) / 10923 ≤ 1
        rw [div_le_one (by norm_num : (0 : ℝ≥0) < 10923)]
        norm_num
      apply NNReal.eq
      rw [NNReal.coe_sub hle]
      norm_num [improvedRadius]
    rw [hr]
    simpa [IRSProfile.repetitions] using
      two_rpow_eighty_seven_div_one_hundred_ge
  calc
    (1 - claimedRadius 2731 10923) ^ IRSProfile.repetitions ≤
        (2 : ℝ≥0) ^ ((87 : ℝ) / 100) / (2 : ℝ≥0) ^ (54 : ℕ) := by
      apply (le_div_iff₀ (by positivity)).2
      simpa [mul_comm] using hscaled
    _ = claimedError 5313 := by
      unfold claimedError
      rw [show -((((5313 : ℕ) : ℝ) / 100)) =
          -((54 : ℕ) : ℝ) + (87 : ℝ) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num [div_eq_mul_inv, mul_comm]

end ProximityPrize.SubmissionLower
