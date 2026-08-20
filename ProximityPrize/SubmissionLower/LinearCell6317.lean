/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.SurfaceFactors6317

/-!
# Degree-one cells by separable quadraticization

The Appendix-A weight theorem genuinely needs `degY R ≥ 2`.  Rather than conceal that endpoint,
we multiply a linear `R` by a fresh scalar linear factor.  The fresh factor is chosen not to meet
the specialized root set, so the product remains separable.  Its `Z+Y` grade rises by exactly one,
which fits because the interpolation grading is strict.  The resulting cell is sent through the
fully proved quadratic heavy-cell theorem.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate ToRatFunc
open scoped BigOperators

namespace RF6317
noncomputable section LinearCell
namespace LinearCell

open Grading6317 Genericity6317
open HenselNumerators Place HeavyCell

variable {F : Type} [Field F]

/-- A deterministic scalar which is not a root of a nonzero linear polynomial. -/
noncomputable def freshShift (S : F[X][Y]) : F :=
  if S.eval 0 ≠ 0 then 0 else 1

theorem eval_freshShift_ne_zero {S : F[X][Y]} (hdeg : S.natDegree = 1) :
    S.eval (Polynomial.C (freshShift S)) ≠ 0 := by
  classical
  by_cases h₀ : S.eval 0 ≠ 0
  · simpa [freshShift, h₀]
  · simp only [freshShift, h₀, if_false]
    intro h₁
    have hc₀ : S.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact not_ne_iff.mp h₀
    have hform := Polynomial.eq_X_add_C_of_natDegree_le_one (p := S) (by omega)
    have hc₁ : S.coeff 1 = 0 := by
      have := h₁
      rw [hform] at this
      simpa [hc₀] using this
    have hlead : S.leadingCoeff = 0 := by
      simpa [Polynomial.leadingCoeff, hdeg] using hc₁
    exact Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < S.natDegree)) hlead

/-- Multiply by a fresh scalar factor in `Y`. -/
noncomputable def quadraticize (x₀ : F) (R : F[X][X][Y]) : F[X][X][Y] :=
  R * (Polynomial.X - Polynomial.C
    (Polynomial.C (Polynomial.C (freshShift (specializeX x₀ R)))))

private theorem freshFactor_ne_zero (x₀ : F) (R : F[X][X][Y]) :
    (Polynomial.X - Polynomial.C
      (Polynomial.C (Polynomial.C (freshShift (specializeX x₀ R)))) : F[X][X][Y]) ≠ 0 :=
  (Polynomial.monic_X_sub_C _).ne_zero

theorem quadraticize_natDegree {x₀ : F} {R : F[X][X][Y]}
    (hR : R ≠ 0) (hdeg : R.natDegree = 1) :
    (quadraticize x₀ R).natDegree = 2 := by
  rw [quadraticize, Polynomial.natDegree_mul hR (freshFactor_ne_zero x₀ R)]
  simp [hdeg]

theorem quadraticize_degreeX {x₀ : F} {R : F[X][X][Y]}
    (hR : R ≠ 0) :
    Bivariate.degreeX (quadraticize x₀ R) = Bivariate.degreeX R := by
  rw [quadraticize, Bivariate.degreeX_mul _ _ hR (freshFactor_ne_zero x₀ R)]
  simp [Bivariate.degreeX]

theorem quadraticize_yzDegree {x₀ : F} {R : F[X][X][Y]}
    (hR : R ≠ 0) :
    yzDegree (quadraticize x₀ R) = yzDegree R + 1 := by
  rw [quadraticize, yzDegree_mul hR (freshFactor_ne_zero x₀ R)]
  simp [yzDegree, swapZX, Bivariate.totalDegree]

theorem specializeX_quadraticize (x₀ : F) (R : F[X][X][Y]) :
    specializeX x₀ (quadraticize x₀ R) =
      specializeX x₀ R *
        (Polynomial.X - Polynomial.C
          (Polynomial.C (freshShift (specializeX x₀ R)))) := by
  simp [quadraticize, specializeX_eq_map]

theorem specializeR_dvd_quadraticize (x₀ z : F) (R : F[X][X][Y]) :
    specializeR R z ∣ specializeR (quadraticize x₀ R) z := by
  unfold quadraticize specializeR
  rw [Polynomial.map_mul]
  exact dvd_mul_right _ _

theorem quadraticize_separable
    {x₀ : F} {R : F[X][X][Y]}
    (hdeg : (specializeX x₀ R).natDegree = 1)
    (hsep : ((specializeX x₀ R).map (univPolyHom (F := F))).Separable) :
    ((specializeX x₀ (quadraticize x₀ R)).map
      (univPolyHom (F := F))).Separable := by
  classical
  let S : F[X][Y] := specializeX x₀ R
  let c : F := freshShift S
  let φ := univPolyHom (F := F)
  have hc : S.eval (Polynomial.C c) ≠ 0 := by
    simpa [S, c] using eval_freshShift_ne_zero hdeg
  have hcmap : (S.map φ).eval (Polynomial.C (φ (Polynomial.C c))) ≠ 0 := by
    rw [Polynomial.eval_map]
    simpa using RationalFunctions.univPolyHom_injective (F := F) hc
  have hcop : IsCoprime (S.map φ)
      (Polynomial.X - Polynomial.C (φ (Polynomial.C c))) := by
    refine ((Polynomial.irreducible_X_sub_C (φ (Polynomial.C c))).coprime_iff_not_dvd.mpr ?_).symm
    rw [Polynomial.dvd_iff_isRoot]
    exact hcmap
  rw [specializeX_quadraticize, Polynomial.map_mul]
  simpa [S, c, φ] using hsep.mul Polynomial.separable_X_sub_C hcop

theorem quadraticized_hypotheses
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hdeg : (specializeX x₀ R).natDegree = 1) :
    Hypotheses x₀ (quadraticize x₀ R) H where
  dvd_evalX := by
    rw [← specializeX, specializeX_quadraticize]
    exact hHyp.dvd_evalX.trans (dvd_mul_right _ _)
  separable_evalX := quadraticize_separable hdeg hHyp.separable_evalX

/-! ## Transfer of a cell to the quadratic theorem -/

theorem card_linear_cell_le_quadratic_core_add_targetN
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (C : HeavyCell.Data U x₀ R H hHyp)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hR : R ≠ 0) (hRdeg : R.natDegree = 1)
    (hSdeg : (specializeX x₀ R).natDegree = 1)
    (hyz : yzDegree R < D) :
    C.scalars.card ≤ 2 * targetDX * 3 * H.natDegree * D + targetN := by
  classical
  let R₂ := quadraticize x₀ R
  let hHyp₂ : Hypotheses x₀ R₂ H := quadraticized_hypotheses hHyp hSdeg
  let C₂ : HeavyCell.Data U x₀ R₂ H hHyp₂ := {
    scalars := C.scalars
    decode := C.decode
    root := C.root
    base := C.base
    factor := fun z ⇒ (C.factor z).trans (specializeR_dvd_quadraticize x₀ z.1 R) }
  have hR₂deg : Bivariate.natDegreeY R₂ = 2 := by
    simpa [R₂, Bivariate.natDegreeY] using quadraticize_natDegree hR hRdeg
  have hD_R₂ : ∀ j ∈ R₂.support,
      Bivariate.degreeX (R₂.coeff j) + j ≤ D := by
    intro j hj
    exact (yzDegree_coeff_le R₂ hj).trans (by
      rw [R₂, quadraticize_yzDegree hR]
      omega)
  have hcell := HeavyCell.card_cell_le_corrected_core_add_targetN
    U x₀ R₂ H hHyp₂ C₂ hD_H hD_R₂ (by omega)
  simpa [C₂, hR₂deg] using hcell

/-- Unified per-cell bound.  The indicator is the explicit, globally affordable cost of sending
a degree-one surface through the degree-two theorem. -/
theorem card_cell_le_with_linear_penalty
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (x₀ : IRSProfile.Field)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (C : HeavyCell.Data U x₀ R H hHyp)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ j ∈ R.support, Bivariate.degreeX (R.coeff j) + j ≤ D)
    (hR : R ≠ 0) (hRpos : 0 < Bivariate.natDegreeY R)
    (hSdegree : (specializeX x₀ R).natDegree = R.natDegree)
    (hyzStrict : yzDegree R < D) :
    C.scalars.card ≤
      2 * targetDX * (Bivariate.natDegreeY R + 1 +
        (if Bivariate.natDegreeY R = 1 then 1 else 0)) * H.natDegree * D + targetN := by
  by_cases hlinear : Bivariate.natDegreeY R = 1
  · have h := card_linear_cell_le_quadratic_core_add_targetN U x₀ R H hHyp C
      hD_H hR (by simpa [Bivariate.natDegreeY] using hlinear)
      (by simpa [Bivariate.natDegreeY, hlinear] using hSdegree) hyzStrict
    simpa [hlinear] using h
  · have hRdeg : 2 ≤ Bivariate.natDegreeY R := by omega
    have h := HeavyCell.card_cell_le_corrected_core_add_targetN
      U x₀ R H hHyp C hD_H hD_R hRdeg
    simpa [hlinear] using h

end LinearCell
end LinearCell
end ProximityPrize.SubmissionLower.RF6317
