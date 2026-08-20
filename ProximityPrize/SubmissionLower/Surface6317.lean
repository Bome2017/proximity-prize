/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.FactorExtraction6317

/-!
# The complete factor-cell cover

This file joins interpolation, primitive surface extraction, honest generic specialization,
the local content exception, rational-place construction, the repaired Hensel cell theorem, and
the aggregate `DY^2` count.  Every choice is made from a proved finite witness.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open scoped BigOperators ENNReal NNReal

namespace Surface6317

open Grading6317 Genericity6317 SurfaceFactors6317 FactorExtraction6317
open RF6317 RF6317.HenselNumerators RF6317.HeavyCell RF6317.LinearCell

noncomputable section

/-! ## Canonical data for one received affine line -/

noncomputable def badScalars
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) : Finset IRSProfile.Field :=
  Finset.univ.filter fun z ⇒
    IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode z U
      (targetRadius : ℝ)

theorem isMCA_of_mem_badScalars
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field} {z : IRSProfile.Field}
    (hz : z ∈ badScalars U) :
    IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode z U
      (targetRadius : ℝ) := by
  exact (Finset.mem_filter.mp hz).2

noncomputable def badDecode
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (hz : z ∈ badScalars U) : TargetDecode U z :=
  Classical.choice (exists_targetDecode U z (isMCA_of_mem_badScalars hz))

noncomputable def interpolant
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) :
    TargetInterpolant IRSProfile.domain (U 0) (U 1) :=
  Classical.choice (exists_targetInterpolant IRSProfile.domain (U 0) (U 1))

abbrev SurfaceIndexOf (Q : IRSProfile.Field[X][X][Y]) :=
  {R // R ∈ surfaceFactors Q}

theorem surface_ne_zero {Q : IRSProfile.Field[X][X][Y]}
    (r : SurfaceIndexOf Q) : r.1 ≠ 0 :=
  (irreducible_of_mem_surfaceFactors r.2).ne_zero

theorem surface_natDegree_pos {Q : IRSProfile.Field[X][X][Y]}
    (r : SurfaceIndexOf Q) : 0 < r.1.natDegree :=
  natDegree_pos_of_mem_surfaceFactors r.2

theorem surface_dvd {Q : IRSProfile.Field[X][X][Y]}
    (r : SurfaceIndexOf Q) : r.1 ∣ Q := dvd_of_mem_surfaceFactors r.2

theorem surface_natDegree_le_target
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) : r.1.natDegree ≤ targetDY := by
  have hle := Polynomial.natDegree_le_of_dvd (surface_dvd r) I.polynomial_ne_zero
  exact hle.trans I.Y_degree.le

theorem surface_xDegree_le_target
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) : Bivariate.degreeX r.1 ≤ targetDX :=
  (targetInterpolant_factor_grades I (surface_ne_zero r) (surface_dvd r)).1

noncomputable def surfacePoint
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) : IRSProfile.Field :=
  Classical.choose (exists_target_specialization
    (irreducible_of_mem_surfaceFactors r.2) (surface_natDegree_pos r)
    (surface_natDegree_le_target I r) (surface_xDegree_le_target I r))

theorem surfacePoint_spec
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) :
    (specializeX (surfacePoint I r) r.1).natDegree = r.1.natDegree ∧
      ((specializeX (surfacePoint I r) r.1).map
        (ToRatFunc.univPolyHom (F := IRSProfile.Field))).Separable :=
  Classical.choose_spec (exists_target_specialization
    (irreducible_of_mem_surfaceFactors r.2) (surface_natDegree_pos r)
    (surface_natDegree_le_target I r) (surface_xDegree_le_target I r))

noncomputable def specializedSurface
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) : IRSProfile.Field[X][Y] :=
  specializeX (surfacePoint I r) r.1

abbrev LocalFactorIndex
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) :=
  {H // H ∈ (positiveDegreeFactors (specializedSurface I r).primPart).toFinset}

theorem localFactor_mem
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    {r : SurfaceIndexOf I.polynomial} (h : LocalFactorIndex I r) :
    h.1 ∈ positiveDegreeFactors (specializedSurface I r).primPart :=
  Multiset.mem_toFinset.mp h.2

theorem localFactor_irreducible
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    {r : SurfaceIndexOf I.polynomial} (h : LocalFactorIndex I r) :
    Irreducible h.1 := irreducible_of_mem_positiveDegreeFactors (localFactor_mem h)

theorem localFactor_degree_pos
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    {r : SurfaceIndexOf I.polynomial} (h : LocalFactorIndex I r) :
    0 < h.1.natDegree := mem_positiveDegreeFactors_degree_pos (localFactor_mem h)

theorem localFactor_dvd_specialized
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    {r : SurfaceIndexOf I.polynomial} (h : LocalFactorIndex I r) :
    h.1 ∣ specializedSurface I r := by
  have hp : h.1 ∣ (specializedSurface I r).primPart :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      (mem_normalizedFactors_of_mem_positiveDegreeFactors (localFactor_mem h))
  exact hp.trans ⟨Polynomial.C (specializedSurface I r).content, by
    rw [Polynomial.eq_C_content_mul_primPart]
    ring⟩

/-! ## Degree and content budgets -/

theorem totalDegree_le_of_dvd
    {A B : IRSProfile.Field[X][Y]} (hA : A ≠ 0) (hB : B ≠ 0) (h : A ∣ B) :
    Bivariate.totalDegree A ≤ Bivariate.totalDegree B := by
  obtain ⟨C, rfl⟩ := h
  have hC : C ≠ 0 := by
    intro hzero
    exact hB (by simp [hzero])
  rw [Bivariate.totalDegree_mul hA hC]
  exact Nat.le_add_right _ _

theorem specializedSurface_ne_zero
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) : specializedSurface I r ≠ 0 := by
  intro hzero
  have hsep := (surfacePoint_spec I r).2
  exact hsep.ne_zero (by simp [specializedSurface, hzero])

theorem specializedSurface_totalDegree_le_yzDegree
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) :
    Bivariate.totalDegree (specializedSurface I r) ≤ yzDegree r.1 := by
  exact RF6317.HenselNumerators.evalX_totalDegree_le_of_coeff_bound
    (surfacePoint I r) r.1 (fun j hj ⇒ yzDegree_coeff_le r.1 hj)

theorem localFactor_totalDegree_le_yzDegree
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) (h : LocalFactorIndex I r) :
    Bivariate.totalDegree h.1 ≤ yzDegree r.1 :=
  (totalDegree_le_of_dvd (localFactor_irreducible h).ne_zero
    (specializedSurface_ne_zero I r) (localFactor_dvd_specialized h)).trans
      (specializedSurface_totalDegree_le_yzDegree I r)

theorem specializedContent_natDegree_le_yzDegree
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) :
    (specializedSurface I r).content.natDegree ≤ yzDegree r.1 := by
  have hS := specializedSurface_ne_zero I r
  have hc : (specializedSurface I r).content ≠ 0 := by
    simpa [Polynomial.content_eq_zero_iff] using hS
  have hle := totalDegree_le_of_dvd (Polynomial.C_ne_zero.mpr hc) hS
    (Polynomial.C_content_dvd (specializedSurface I r))
  have hC : Bivariate.totalDegree
      (Polynomial.C (specializedSurface I r).content) =
        (specializedSurface I r).content.natDegree := by
    simp [Bivariate.totalDegree, Bivariate.natDegreeY]
  rw [hC] at hle
  exact hle.trans (specializedSurface_totalDegree_le_yzDegree I r)

noncomputable def localContentRootSet
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) : Finset IRSProfile.Field :=
  Finset.univ.biUnion fun r : SurfaceIndexOf I.polynomial ⇒
    contentRootSet (specializedSurface I r)

noncomputable def exceptionalContent
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) : Finset IRSProfile.Field :=
  globalContentRootSet I.polynomial ∪ localContentRootSet I

theorem localContentRootSet_card_le
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) :
    (localContentRootSet I).card ≤
      ∑ r : SurfaceIndexOf I.polynomial, yzDegree r.1 := by
  classical
  calc
    (localContentRootSet I).card ≤
        ∑ r : SurfaceIndexOf I.polynomial,
          (contentRootSet (specializedSurface I r)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ r : SurfaceIndexOf I.polynomial, yzDegree r.1 := by
      apply Finset.sum_le_sum
      intro r _
      exact (contentRootSet_card_le (specializedSurface I r) (by
        simpa [Polynomial.content_eq_zero_iff] using specializedSurface_ne_zero I r)).trans
          (specializedContent_natDegree_le_yzDegree I r)

theorem exceptionalContent_card_le_targetDZ
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) :
    (exceptionalContent I).card ≤ targetDZ := by
  classical
  calc
    (exceptionalContent I).card ≤
        (globalContentRootSet I.polynomial).card + (localContentRootSet I).card :=
      Finset.card_union_le _ _
    _ ≤ Bivariate.degreeX I.polynomial.content +
          ∑ r : SurfaceIndexOf I.polynomial, yzDegree r.1 := by
      exact Nat.add_le_add
        (globalContentRootSet_card_le_degreeX I.polynomial I.polynomial_ne_zero)
        (localContentRootSet_card_le I)
    _ ≤ yzDegree I.polynomial := by
      simpa [SurfaceIndexOf] using
        content_degreeX_add_sum_yzDegree_surfaceFactors_le
          I.polynomial I.polynomial_ne_zero
    _ ≤ targetDZ := (targetInterpolant_yzDegree_lt I).le

/-! ## Cells and their Hensel data -/

noncomputable def factorCell
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r) :
    Finset IRSProfile.Field :=
  (badScalars U).filter fun z ⇒
    if hz : z ∈ badScalars U then
      (Polynomial.X - Polynomial.C (badDecode U z hz).polynomial ∣
          specializeR p.1.1 z) ∧
        evalZY p.2.1 z
          ((badDecode U z hz).polynomial.eval (surfacePoint I p.1)) = 0
    else False

theorem factorCell_subset_bad
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    (p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r) :
    factorCell U I p ⊆ badScalars U := Finset.filter_subset _ _

theorem factorCell_conditions
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {I : TargetInterpolant IRSProfile.domain (U 0) (U 1)}
    (p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r)
    {z : IRSProfile.Field} (hz : z ∈ factorCell U I p) :
    let hzbad : z ∈ badScalars U := factorCell_subset_bad p hz
    (Polynomial.X - Polynomial.C (badDecode U z hzbad).polynomial ∣
        specializeR p.1.1 z) ∧
      evalZY p.2.1 z
        ((badDecode U z hzbad).polynomial.eval (surfacePoint I p.1)) = 0 := by
  classical
  let hzbad : z ∈ badScalars U := factorCell_subset_bad p hz
  have h := (Finset.mem_filter.mp hz).2
  simpa [factorCell, hzbad] using h

theorem localFactor_hypotheses
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) (h : LocalFactorIndex I r) :
    Hypotheses (surfacePoint I r) r.1 h.1 where
  dvd_evalX := by
    simpa [specializedSurface] using localFactor_dvd_specialized h
  separable_evalX := (surfacePoint_spec I r).2

noncomputable def cellData
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r) :
    letI : Fact (Irreducible p.2.1) := ⟨localFactor_irreducible p.2⟩
    letI : Fact (0 < p.2.1.natDegree) := ⟨localFactor_degree_pos p.2⟩
    HeavyCell.Data U (surfacePoint I p.1) p.1.1 p.2.1
      (localFactor_hypotheses I p.1 p.2) := by
  classical
  letI : Fact (Irreducible p.2.1) := ⟨localFactor_irreducible p.2⟩
  letI : Fact (0 < p.2.1.natDegree) := ⟨localFactor_degree_pos p.2⟩
  let E := factorCell U I p
  let hHyp := localFactor_hypotheses I p.1 p.2
  exact {
    scalars := E
    decode := fun z ⇒ badDecode U z.1 (factorCell_subset_bad p z.2)
    root := fun z hz ⇒ by
      let hzbad : z ∈ badScalars U := factorCell_subset_bad p hz
      have hroot := (factorCell_conditions p hz).2
      have hroot' : p.2.1.evalEval z
          ((badDecode U z hzbad).polynomial.eval (surfacePoint I p.1)) = 0 := by
        simpa [evalZY] using hroot
      exact scaledRationalRoot (localFactor_degree_pos p.2) z
        ((badDecode U z hzbad).polynomial.eval (surfacePoint I p.1)) hroot'
    base := fun z ⇒ by
      simp [scaledRationalRoot]
    factor := fun z ⇒ (factorCell_conditions p z.2).1 }

theorem factorCell_card_le
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r) :
    (factorCell U I p).card ≤
      2 * targetDX * (p.1.1.natDegree + 1 +
        (if p.1.1.natDegree = 1 then 1 else 0)) *
          p.2.1.natDegree * targetDZ + targetN := by
  classical
  letI : Fact (Irreducible p.2.1) := ⟨localFactor_irreducible p.2⟩
  letI : Fact (0 < p.2.1.natDegree) := ⟨localFactor_degree_pos p.2⟩
  let hHyp := localFactor_hypotheses I p.1 p.2
  let C := cellData U I p
  have hRgrade : ∀ j ∈ p.1.1.support,
      Bivariate.degreeX (p.1.1.coeff j) + j ≤ targetDZ :=
    targetInterpolant_factor_hensel_grade I (surface_ne_zero p.1) (surface_dvd p.1)
  have hyz : yzDegree p.1.1 < targetDZ :=
    (yzDegree_le_of_dvd (surface_ne_zero p.1) I.polynomial_ne_zero
      (surface_dvd p.1)).trans_lt (targetInterpolant_yzDegree_lt I)
  have h := card_cell_le_with_linear_penalty U (surfacePoint I p.1) p.1.1 p.2.1
    hHyp C (localFactor_totalDegree_le_yzDegree I p.1 p.2 |>.trans hyz.le)
    hRgrade (surface_ne_zero p.1) (surface_natDegree_pos p.1)
    (surfacePoint_spec I p.1).1 hyz
  simpa [C, cellData, Bivariate.natDegreeY] using h

/-! ## Every bad scalar is covered -/

theorem badScalars_cover
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) :
    badScalars U ⊆ exceptionalContent I ∪
      Finset.univ.biUnion (factorCell U I) := by
  classical
  intro z hzbad
  by_cases hzglobal : z ∈ globalContentRootSet I.polynomial
  · exact Finset.mem_union_left _ (by
      exact Finset.mem_union_left _ hzglobal)
  · let d := badDecode U z hzbad
    have hQdiv : Polynomial.X - Polynomial.C d.polynomial ∣
        specializeZ I.polynomial z := targetDecode_dvd_specialized U I d
    obtain ⟨R, hR, hRdiv⟩ := exists_surface_factor_of_linear_dvd
      I.polynomial_ne_zero hzglobal hQdiv
    let r : SurfaceIndexOf I.polynomial := ⟨R, hR⟩
    let S := specializedSurface I r
    have hSroot : evalZY S z (d.polynomial.eval (surfacePoint I r)) = 0 := by
      exact evalZY_specializeX_eq_zero_of_linear_dvd hRdiv
    by_cases hzlocal : z ∈ contentRootSet S
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨r, Finset.mem_univ _, by simpa [S]⟩
    · obtain ⟨H, hH, hHroot⟩ :=
        exists_positive_factor_of_evalZY_primPart_eq_zero S z
          (d.polynomial.eval (surfacePoint I r))
          (evalZY_primPart_eq_zero_of_not_contentRoot S z _ hSroot hzlocal)
      let h : LocalFactorIndex I r := ⟨H, Multiset.mem_toFinset.mpr hH⟩
      let p : Σ r : SurfaceIndexOf I.polynomial, LocalFactorIndex I r := ⟨r, h⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨p, Finset.mem_univ _, ?_⟩
      simp only [factorCell, Finset.mem_filter, hzbad, true_and, dif_pos]
      constructor
      · simpa [p, r, d] using hRdiv
      · simpa [p, r, h, d] using hHroot

/-! ## Aggregate factor degrees -/

theorem sum_surface_natDegree_le
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1)) :
    ∑ r : SurfaceIndexOf I.polynomial, r.1.natDegree ≤ targetDY := by
  simpa [SurfaceIndexOf] using
    (sum_natDegree_surfaceFactors_le I.polynomial).trans I.Y_degree.le

theorem sum_localFactor_natDegree_le
    {U : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (I : TargetInterpolant IRSProfile.domain (U 0) (U 1))
    (r : SurfaceIndexOf I.polynomial) :
    ∑ h : LocalFactorIndex I r, h.1.natDegree ≤ r.1.natDegree := by
  calc
    ∑ h : LocalFactorIndex I r, h.1.natDegree =
        ∑ H ∈ (positiveDegreeFactors (specializedSurface I r).primPart).toFinset,
          H.natDegree := by simp [LocalFactorIndex]
    _ ≤ (specializedSurface I r).primPart.natDegree :=
      sum_natDegree_toFinset_positiveDegreeFactors_le _
    _ = (specializedSurface I r).natDegree := Polynomial.natDegree_primPart _
    _ = r.1.natDegree := (surfacePoint_spec I r).1

/-- The complete exceptional-scalar count for a fixed received affine line. -/
theorem badScalars_card_le_target
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field) :
    (badScalars U).card ≤ targetMcaNumerator := by
  classical
  let I := interpolant U
  have hcount := bad_card_le_of_factor_cells_with_linear_penalty
    (fun r : SurfaceIndexOf I.polynomial ⇒ LocalFactorIndex I r)
    (badScalars U) (exceptionalContent I) (factorCell U I)
    (fun r ⇒ r.1.natDegree) (fun _ ⇒ targetDZ)
    (fun _ h ⇒ h.1.natDegree)
    (badScalars_cover U I) (exceptionalContent_card_le_targetDZ I)
    (factorCell_card_le U I)
    (fun _ h ⇒ localFactor_degree_pos h)
    (sum_localFactor_natDegree_le I)
    (sum_surface_natDegree_le I) (fun _ ⇒ le_rfl)
  exact hcount.trans (by
    change targetDZ + targetIntegerMcaNumerator ≤ targetMcaNumerator
    exact targetIntegerMcaNumerator_le_target)

theorem targetBadScalarBound : TargetBadScalarBound := by
  intro U
  simpa [badScalars] using badScalars_card_le_target U

end
end Surface6317
end ProximityPrize.SubmissionLower
