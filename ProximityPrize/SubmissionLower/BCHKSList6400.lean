import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.JohnsonFamily

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable abbrev BCHKS6400SquaredCode :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
      IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem bchks6400_squaredCode_minDistance :
    Code.minDist BCHKS6400SquaredCode = 131073 := by
  calc
    Code.minDist BCHKS6400SquaredCode =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

theorem bchks6400_lambda_le :
    Code.Lambda BCHKS6400SquaredCode (bchksRadius6400 : ℝ) ≤
      (bchksListBound6400 : ℕ∞) := by
  have hJ : Code.Lambda BCHKS6400SquaredCode
      (JohnsonBound.Jqℓ (Fintype.card IRSProfile.Field) 200000 (131073 / 262144 : ℚ)) ≤
      (200000 : ℕ∞) :=
    CodingTheory.johnson_bound_lambda_le_ell BCHKS6400SquaredCode 200000 (by norm_num)
  have hle : (bchksRadius6400 : ℝ) ≤
      JohnsonBound.Jqℓ (Fintype.card IRSProfile.Field) 200000 (131073 / 262144 : ℚ) := by
    unfold JohnsonBound.Jqℓ JohnsonBound.J bchksRadius6400
    have hq : (2 : ℚ) ≤ (Fintype.card IRSProfile.Field : ℚ) := by
      have : 2 ≤ Fintype.card IRSProfile.Field := by
        have hcard : Fintype.card IRSProfile.Field = 2130706433 ^ 6 := by
          simp [IRSProfile.Field, KoalaBear.Field, KoalaBear.Ext6]
          native_decide
        rw [hcard]; norm_num
      exact_mod_cast this
    have hsqrt_upper : Real.sqrt (1 - ((Fintype.card IRSProfile.Field : ℚ) / ((Fintype.card IRSProfile.Field : ℚ) - 1) * ((199999 : ℚ)/200000) * (131073/262144) : ℚ) : ℝ) < 707107 / 1000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 707107/1000000)]
      norm_num
    have h1 : ((1 - 1 / (Fintype.card IRSProfile.Field : ℚ) : ℚ) : ℝ) > 0.999999 := by
      norm_num
    nlinarith
  calc Code.Lambda BCHKS6400SquaredCode (bchksRadius6400 : ℝ)
      ≤ Code.Lambda BCHKS6400SquaredCode (JohnsonBound.Jqℓ (Fintype.card IRSProfile.Field) 200000 (131073 / 262144 : ℚ)) :=
        Code.Lambda_mono hle
    _ ≤ (200000 : ℕ∞) := hJ

end ProximityPrize.SubmissionLower
