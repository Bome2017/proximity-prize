/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower

/-!
# Exact downstream certificate for the 60.98-bit lower submission

This file contains the protocol and numerical part of the target submission.  The only
mathematical input exposed by the main reduction lemma is the base Reed--Solomon MCA bound at
the target radius; the BCHKS/BCIKS proof of that input lives in separate local helper modules.
-/

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

set_option maxRecDepth 100000

/-- The deliberately simple one-shot target radius. -/
noncomputable def targetRadius : ℝ≥0 := 9 / 32

/-- The two-row code used by the list term of `certifiedGammaError`. -/
noncomputable abbrev TargetSquaredCode : Set (IRSProfile.Index →
    Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem targetSquaredCode_minDistance :
    Code.minDist (TargetSquaredCode : Set (IRSProfile.Index →
      Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) = 131073 := by
  calc
    Code.minDist (TargetSquaredCode : Set (IRSProfile.Index →
        Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) =
      Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field)) := by
          exact Code.minDist_interleavedCodeSet (κ := Fin 2)
            (IRSProfile.code : Set (IRSProfile.Index →
              Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

/-- The exact positive slack between the rate-`1/2` Johnson radius and `targetRadius`. -/
noncomputable def targetListSlack : ℝ :=
  1 - Real.sqrt ((1 : ℝ) / 2) - targetRadius

theorem targetListSlack_pos : 0 < targetListSlack := by
  have hsqrt : Real.sqrt ((1 : ℝ) / 2) < 1 - (targetRadius : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num [targetRadius])).2
    norm_num [targetRadius]
  unfold targetListSlack
  linarith

/-- The real Johnson list bound is strictly below `315`; integrality then gives list size `≤ 314`. -/
theorem target_johnson_real_lt_315 :
    1 / (2 * targetListSlack * ((1 : ℝ) / 2)) < 315 := by
  have hsqrt : Real.sqrt ((1 : ℝ) / 2) <
      1 - (targetRadius : ℝ) - 1 / 315 := by
    apply (Real.sqrt_lt' (by norm_num [targetRadius])).2
    norm_num [targetRadius]
  have hslack : (1 : ℝ) / 315 < targetListSlack := by
    unfold targetListSlack
    linarith
  have hpos := targetListSlack_pos
  rw [show 2 * targetListSlack * ((1 : ℝ) / 2) = targetListSlack by ring]
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- The two-row list contribution at the target radius has at most `314` codewords. -/
theorem targetSquaredCode_lambda_toNat_le_314 :
    (Code.Lambda TargetSquaredCode (targetRadius : ℝ)).toNat ≤ 314 := by
  have hrate :
      (Code.minDist TargetSquaredCode : ℝ) / Fintype.card IRSProfile.Index =
        1 - ((1 : ℝ) / 2) + 1 / Fintype.card IRSProfile.Index := by
    rw [targetSquaredCode_minDistance]
    norm_num [IRSProfile.Index]
  have hj := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    TargetSquaredCode ((1 : ℝ) / 2) targetListSlack
    (by norm_num) (by norm_num) targetListSlack_pos hrate
  have hradius :
      1 - Real.sqrt ((1 : ℝ) / 2) - targetListSlack = (targetRadius : ℝ) := by
    unfold targetListSlack
    ring
  rw [hradius] at hj
  have hfinite : Code.Lambda TargetSquaredCode (targetRadius : ℝ) ≠ ⊤ := by
    intro htop
    rw [htop] at hj
    simp at hj
  have hlt :
      ((Code.Lambda TargetSquaredCode (targetRadius : ℝ)).toNat : ℝ) < 315 := by
    have hcoe :
        (((Code.Lambda TargetSquaredCode (targetRadius : ℝ)).toNat : ℕ) : ENNReal) ≤
          ENNReal.ofReal (1 / (2 * targetListSlack * ((1 : ℝ) / 2))) := by
      simpa [ENat.coe_toNat hfinite] using hj
    have htop' :
        ENNReal.ofReal (1 / (2 * targetListSlack * ((1 : ℝ) / 2))) ≠ ⊤ := by simp
    have hcoe' := ENNReal.toReal_le_toReal (by simp) htop' |>.mpr hcoe
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at hcoe'
    exact hcoe'.trans_lt target_johnson_real_lt_315
  omega

/-- Integer-ceiling numerator for the locally formalized BCHKS count.  This deliberately uses
`n * DY` for the affine exceptional-cell term, avoiding any real-number rounding in the
algebraic proof while retaining ample field-size slack. -/
def targetMcaNumerator : ℕ := 272000000000000000

/-- Combining the target MCA numerator and the two-row list bound clears `2^-128`. -/
theorem certifiedGammaError_target_of_mca
    (hMca : mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (targetRadius : ℝ) ≤
      (targetMcaNumerator : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal)) :
    certifiedGammaError IRSProfile.code targetRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  have hList :
      ((Code.Lambda TargetSquaredCode (targetRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (314 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
    exact ENNReal.div_le_div_right
      (by exact_mod_cast targetSquaredCode_lambda_toNat_le_314) _
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (targetRadius : ℝ) +
        ((Code.Lambda TargetSquaredCode (targetRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
      (targetMcaNumerator : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (314 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add hMca hList
    _ ≤ (((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0) : ENNReal) := by
      have hne :
          (targetMcaNumerator : ENNReal) /
                (Fintype.card IRSProfile.Field : ENNReal) +
              314 / (Fintype.card IRSProfile.Field : ENNReal) ≠ ⊤ := by
        rw [ENNReal.add_ne_top]
        constructor <;> apply ENNReal.div_ne_top <;> simp
      apply (ENNReal.toReal_le_toReal hne (by simp)).mp
      have hparts := ENNReal.add_ne_top.mp hne
      rw [ENNReal.toReal_add hparts.1 hparts.2,
        ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num [targetMcaNumerator, IRSProfile.Field, KoalaBear.Ext6]

/-- A rational upper bracket for the exact spot-check error. -/
theorem target_spotcheck_rational_bound :
    (1 - targetRadius) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (61 : ℕ)) * (259 / 256) := by
  rw [← NNReal.coe_le_coe]
  norm_num [targetRadius, IRSProfile.repetitions, div_le_iff₀]

/-- The rational bracket lies below `2^(2/100)`. -/
theorem target_rational_le_two_rpow :
    (259 : ℝ≥0) / 256 ≤ (2 : ℝ≥0) ^ ((2 : ℝ) / 100) := by
  have hroot :
      (259 : ℝ≥0) / 256 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((50 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 50)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (259 : ℝ≥0) / 256 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((50 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((2 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

/-- The target radius certifies the exact `60.98`-bit score. -/
theorem target_score_6098 :
    (1 - targetRadius) ^ IRSProfile.repetitions ≤
      claimedError 6098 := by
  calc
    (1 - targetRadius) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (61 : ℕ)) * (259 / 256) :=
      target_spotcheck_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (61 : ℕ)) *
          (2 : ℝ≥0) ^ ((2 : ℝ) / 100) := by
      exact mul_le_mul_of_nonneg_left target_rational_le_two_rpow (by positivity)
    _ = claimedError 6098 := by
      unfold claimedError
      rw [show -((((6098 : ℕ) : ℝ) / 100)) =
          -((61 : ℕ) : ℝ) + (2 : ℝ) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

end ProximityPrize.SubmissionLower
