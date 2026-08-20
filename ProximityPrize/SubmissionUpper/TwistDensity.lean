import ProximityPrize.SubmissionUpper.TwistPencil

namespace ProximityPrize.SubmissionUpper

open ProximityPrize.Benchmark

theorem twist_winning_density (δ : ℝ≥0)
    (hlo : (122642 / 262144 : ℝ≥0) ≤ δ) (hhi : δ < 1 / 2) :
    Upper.epsilonStar < ToyProblem.winningSetDensity IRSProfile.encoder δ := by
  have hcard : Fintype.card IRSProfile.Field = 2130706433 ^ 6 := by
    exact KoalaBear.card_ext6.trans (by rfl)
  have hnat : Fintype.card IRSProfile.Field < 2 ^ 58 * 2 ^ 128 := by
    rw [hcard]
    norm_num
  have hfrac : Upper.epsilonStar <
      ((2 ^ 58 : ℕ) : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
    unfold Upper.epsilonStar ProximityGap.prizeThreshold
    rw [ENNReal.div_eq_inv_mul]
    have hpos : (0 : ENNReal) < (Fintype.card IRSProfile.Field : ENNReal) := by positivity
    rw [ENNReal.rpow_neg (by norm_num : (0 : ENNReal) ≤ 2)]
    rw [show (128 : ℝ) = ((128 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [ENNReal.inv_lt_inv hpos.ne' (by positivity : (2 : ENNReal) ^ 128 ≠ 0)]
    rw [div_lt_iff₀ (by positivity : (0 : ENNReal) < (Fintype.card IRSProfile.Field : ENNReal))]
    exact_mod_cast hnat
  have heps := pencil_epsCa_lower δ hlo hhi
  have hbridge := ToyProblem.epsCa_le_winningSetDensity δ (by positivity) (hhi.trans (by norm_num))
    IRSProfile.encoder IRSProfile.encoder_injective IRSProfile.encoder_range
  exact_mod_cast hfrac.trans_le (heps.trans hbridge)

end ProximityPrize.SubmissionUpper
