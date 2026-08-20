/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.MCA6317

/-!
# Exact BCHKS parameters for the 60.98-bit lower submission

This file starts the algebraic part of the submission.  In particular, it records the
*triangular* Guruswami--Sudan monomial support used by BCHKS, rather than replacing it by a
rectangular box.  At the target parameters the dimension surplus is only about 0.22%, so
preserving this support is essential.

The second section proves the elementary Haboeck exceptional-scalar endgame: if every scalar
in a factor cell is witnessed by a coordinate at which a nonconstant affine difference
vanishes, then that cell contains at most one scalar per coordinate.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped BigOperators ENNReal NNReal

/-! ## Concrete interpolation dimensions -/

def targetN : ℕ := 262144
def targetK : ℕ := 131072
def targetM : ℕ := 222
def targetDX : ℕ := 41243289
def targetDY : ℕ := 315
def targetDZ : ℕ := 33005

/-- The exact triangular coefficient support
`0 ≤ j < DY`, `0 ≤ i < DX-kj`, `0 ≤ ell < DZ-j`. -/
abbrev TargetCoefficientIndex :=
  Σ j : Fin targetDY, Fin (targetDX - targetK * j.1) × Fin (targetDZ - j.1)

/-- The exact interpolation constraints: at every domain point, all mixed Hasse derivatives
of total `(Y,Z)` order below `m`, with the remaining `Z` coefficient range. -/
abbrev TargetConstraintIndex :=
  Fin targetN ×
    (Σ s : Fin targetM, Fin (targetM - s.1) × Fin (targetDZ - s.1))

theorem targetCoefficientIndex_card :
    Fintype.card TargetCoefficientIndex = 214164473656560 := by
  norm_num [TargetCoefficientIndex, targetDX, targetDY, targetDZ, targetK,
    Fintype.card_sigma]

theorem targetConstraintIndex_card :
    Fintype.card TargetConstraintIndex = 213686496526336 := by
  norm_num [TargetConstraintIndex, targetN, targetM, targetDZ, Fintype.card_sigma]

/-- The interpolation system has a nonzero kernel over every field. -/
theorem target_constraints_lt_coefficients :
    Fintype.card TargetConstraintIndex < Fintype.card TargetCoefficientIndex := by
  rw [targetConstraintIndex_card, targetCoefficientIndex_card]
  norm_num

/-- Integer ceiling version of the complete BCHKS exceptional-scalar budget.  The first term
is the improved factor-cell sum and the second permits one exceptional scalar per coordinate
for each of the `DY` factor-degree units. -/
def targetIntegerMcaNumerator : ℕ :=
  2 * targetDX * (targetDY ^ 2 + 2 * targetDY) * targetDZ + targetN * targetDY

theorem targetIntegerMcaNumerator_value :
    targetIntegerMcaNumerator = 271852192693076310 := by
  norm_num [targetIntegerMcaNumerator, targetDX, targetDY, targetDZ, targetN]

theorem targetIntegerMcaNumerator_fits_field_budget :
    targetIntegerMcaNumerator + 314 ≤
      Fintype.card IRSProfile.Field / 2 ^ (128 : ℕ) := by
  norm_num [targetIntegerMcaNumerator, targetDX, targetDY, targetDZ, targetN,
    IRSProfile.Field, KoalaBear.Ext6]

theorem targetIntegerMcaNumerator_le_target :
    targetDZ + targetIntegerMcaNumerator ≤ targetMcaNumerator := by
  rw [targetIntegerMcaNumerator_value]
  norm_num [targetMcaNumerator, targetDZ]

/-! ## The affine exceptional-scalar endgame -/

section AffineExceptional

variable {F ι : Type} [Field F] [Fintype F]
variable [Fintype ι] [DecidableEq F] [DecidableEq ι]

/-- At a fixed coordinate a genuinely nonconstant affine function has at most one root. -/
lemma affine_root_unique {a b γ γ' : F} (ha : a ≠ 0)
    (hγ : a * γ + b = 0) (hγ' : a * γ' + b = 0) : γ = γ' := by
  apply (mul_left_cancel₀ ha)
  linear_combination hγ - hγ'

/-- Haboeck's final counting step, in the precise form needed by a factor cell.  Each bad
scalar chooses a coordinate whose affine discrepancy vanishes and whose slope is nonzero.
The chosen coordinate determines the scalar, so there are at most `|ι|` of them. -/
theorem card_le_card_of_affine_coordinate_witness
    (E : Finset F) (slope intercept : ι → F)
    (hwitness : ∀ γ ∈ E, ∃ i : ι,
      slope i ≠ 0 ∧ slope i * γ + intercept i = 0) :
    E.card ≤ Fintype.card ι := by
  classical
  choose witness hwitness_spec using hwitness
  have hinj : Set.InjOn witness (E : Set F) := by
    intro γ hγ γ' hγ' heq
    have hγspec := hwitness_spec γ hγ
    have hγ'spec := hwitness_spec γ' hγ'
    rw [heq] at hγspec
    exact affine_root_unique hγspec.1 hγspec.2 hγ'spec.2
  exact Finset.card_le_card_of_injOn witness (fun _ _ => Finset.mem_univ _) hinj

/-- Target specialization of the one-scalar-per-coordinate bound. -/
theorem target_factor_exception_card_le
    (E : Finset IRSProfile.Field)
    (slope intercept : IRSProfile.Index → IRSProfile.Field)
    (hwitness : ∀ γ ∈ E, ∃ i : IRSProfile.Index,
      slope i ≠ 0 ∧ slope i * γ + intercept i = 0) :
    E.card ≤ targetN := by
  simpa [targetN, IRSProfile.Index] using
    card_le_card_of_affine_coordinate_witness E slope intercept hwitness

end AffineExceptional

end ProximityPrize.SubmissionLower
