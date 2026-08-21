import ProximityPrize.SubmissionLower.BCHKSParameters6399
import ProximityPrize.SubmissionLower.JohnsonLemmas

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable abbrev BCHKS6399SquaredCode :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
      IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem bchks6399_squaredCode_minDistance :
    Code.minDist BCHKS6399SquaredCode = 131073 := by
  calc
    Code.minDist BCHKS6399SquaredCode =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

set_option maxRecDepth 100000 in
theorem bchks6399_lambda_le :
    Code.Lambda BCHKS6399SquaredCode (bchksRadius6399 : ℝ) ≤
      (bchksListBound6399 : ℕ∞) := by
  rw [JohnsonBound.lambda_eq_floor_div_card BCHKS6399SquaredCode (by positivity)]
  rw [show ⌊(bchksRadius6399 : ℝ) *
      Fintype.card IRSProfile.Index⌋₊ = 76770 by
    norm_num [bchksRadius6399, IRSProfile.Index]]
  norm_num [IRSProfile.Index, bchksListBound6399]
  convert JohnsonBound.lambda_le_3519_of_minDist BCHKS6399SquaredCode
    (by norm_num [IRSProfile.Index]) bchks6399_squaredCode_minDistance using 1 <;> norm_num

end ProximityPrize.SubmissionLower
