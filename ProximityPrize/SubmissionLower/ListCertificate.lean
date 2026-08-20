import ProximityPrize.SubmissionLower.RSListDecodability
import ProximityPrize.SubmissionLower.InterleavedListBound

namespace ProximityPrize.SubmissionLower

open Code ProximityPrize.Benchmark
open scoped ENNReal NNReal

noncomputable def ImprovedRadius : ℝ := (65542 : ℝ) / 262144

private noncomputable def ProfileDelta : ℝ := (131073 : ℝ) / 262144

private theorem profile_branching_eq_two :
    ⌈ImprovedRadius / (ProfileDelta - ImprovedRadius)⌉₊ = 2 := by
  apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).2
  constructor <;> norm_num [ImprovedRadius, ProfileDelta]

private theorem profile_depth_eq_two :
    ⌈Real.log (ProfileDelta / (ProfileDelta - ImprovedRadius)) / Real.log 2⌉₊ = 2 := by
  apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio_pos : 0 < ProfileDelta / (ProfileDelta - ImprovedRadius) := by
    norm_num [ProfileDelta, ImprovedRadius]
  have hratio_lower : (2 : ℝ) < ProfileDelta / (ProfileDelta - ImprovedRadius) := by
    norm_num [ProfileDelta, ImprovedRadius]
  have hratio_upper : ProfileDelta / (ProfileDelta - ImprovedRadius) < (4 : ℝ) := by
    norm_num [ProfileDelta, ImprovedRadius]
  constructor
  · rw [lt_div_iff₀ hlog2]
    simpa using Real.strictMonoOn_log (by norm_num) hratio_pos hratio_lower
  · apply (div_le_iff₀ hlog2).2
    have hlog := Real.strictMonoOn_log hratio_pos (by norm_num) hratio_upper
    norm_num
    calc
      Real.log (ProfileDelta / (ProfileDelta - ImprovedRadius)) ≤ Real.log 4 := hlog.le
      _ = (2 : ℝ) * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num

private theorem profile_sqrtRate_sq :
    (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ) ^ 2 = 1 / 2 := by
  rw [ReedSolomon.sqrtRate_sq]
  norm_num [IRSProfile.baseDimension, IRSProfile.Index]

private theorem profile_sqrtRate_upper :
    (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ) ≤ 177 / 250 := by
  have hs := ReedSolomon.sqrtRate_nonneg IRSProfile.baseDimension IRSProfile.domain
  have hsq := profile_sqrtRate_sq
  nlinarith

private theorem profile_sqrtRate_lower :
    (25 : ℝ) / 36 <
      (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ) := by
  have hs := ReedSolomon.sqrtRate_nonneg IRSProfile.baseDimension IRSProfile.domain
  have hsq := profile_sqrtRate_sq
  nlinarith

theorem base_lambda_improved_le_seventeen :
    Code.Lambda
      (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field))
      ImprovedRadius ≤ 17 := by
  have hr : ImprovedRadius ≤
      1 - (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ) -
        (1 / 25 : ℝ) := by
    unfold ImprovedRadius
    nlinarith [profile_sqrtRate_upper]
  have hld := ReedSolomon.listDecodable_reedSolomon IRSProfile.domain
    (m := IRSProfile.baseDimension) (by norm_num [IRSProfile.baseDimension])
    (η := (1 / 25 : ℝ≥0)) (by norm_num)
  have hsmall := hld.anti_radius hr
  rw [Code.isListDecodable_iff_Lambda_le] at hsmall
  refine hsmall.trans ?_
  have hspos : 0 <
      (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ) :=
    profile_sqrtRate_lower.trans' (by norm_num)
  have hell :
      (1 / (2 * (1 / 25 : ℝ≥0) *
        ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain) : ℝ) < 18 := by
    rw [div_lt_iff₀]
    · calc
        (1 : ℝ) = 18 * (2 * (1 / 25) * (25 / 36)) := by norm_num
        _ < 18 * (2 * (1 / 25) *
            (ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain : ℝ)) := by
          gcongr
          exact profile_sqrtRate_lower
    · exact_mod_cast mul_pos (by norm_num : (0 : ℝ≥0) < 2 * (1 / 25))
        (show (0 : ℝ≥0) < ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain by
          exact_mod_cast hspos)
  have hfloor :
      ⌊(1 / (2 * (1 / 25 : ℝ≥0) *
        ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain) : ℝ≥0)⌋₊ < 18 := by
    apply (Nat.floor_lt (by positivity)).2
    exact hell
  exact_mod_cast (by omega :
    ⌊(1 / (2 * (1 / 25 : ℝ≥0) *
      ReedSolomon.sqrtRate IRSProfile.baseDimension IRSProfile.domain) : ℝ≥0)⌋₊ ≤ 17)

private theorem lambda_interleaved_profile_le
    {A : Type} [Finite A] [DecidableEq A]
    (C : Set (IRSProfile.Index → A))
    (hmin : Code.minDist C = 131073)
    (m L : ℕ) (hm : 1 ≤ m)
    (hL : Code.Lambda C ImprovedRadius ≤ L) :
    Code.Lambda (Code.interleavedCodeSet (κ := Fin m) C) ImprovedRadius ≤
      6 * L ^ 2 := by
  have hub : ImprovedRadius <
      (Code.minDist C : ℝ) / Fintype.card IRSProfile.Index := by
    rw [hmin]
    norm_num [ImprovedRadius, IRSProfile.Index]
  have hg := InterleavedCode.lambda_interleaved_le_choose_mul_pow
    C ImprovedRadius m hm (by norm_num [ImprovedRadius]) hub
  let deltaC : ℝ := (Code.minDist C : ℝ) / Fintype.card IRSProfile.Index
  let eta : ℝ := deltaC - ImprovedRadius
  let b : ℕ := ⌈ImprovedRadius / eta⌉₊
  let r : ℕ := ⌈Real.log (deltaC / eta) / Real.log 2⌉₊
  change Code.Lambda (Code.interleavedCodeSet (κ := Fin m) C) ImprovedRadius ≤
    ((b + r).choose r : ℕ∞) * (Code.Lambda C ImprovedRadius) ^ r at hg
  have hdeltaC : deltaC = ProfileDelta := by
    simp [deltaC, ProfileDelta, hmin, IRSProfile.Index]
  have hb : b = 2 := by
    simpa [b, eta, hdeltaC] using profile_branching_eq_two
  have hr : r = 2 := by
    simpa [r, eta, hdeltaC] using profile_depth_eq_two
  rw [hb, hr] at hg
  norm_num [Nat.choose] at hg
  exact hg.trans (by gcongr)

theorem irs_lambda_improved_le_1734 :
    Code.Lambda
      (IRSProfile.code : Set (IRSProfile.Index →
        Fin IRSProfile.interleaving → IRSProfile.Field))
      ImprovedRadius ≤ 1734 := by
  have h := lambda_interleaved_profile_le
      (IRSProfile.baseCode : Set (IRSProfile.Index → IRSProfile.Field))
      IRSProfile.baseMinDistance IRSProfile.interleaving 17
      (by norm_num [IRSProfile.interleaving]) base_lambda_improved_le_seventeen
  norm_num at h
  simpa [IRSProfile.code, IRSProfile.baseCode,
    ReedSolomon.Interleaved.irsCode,
    IRSProfile.totalDimension_div_interleaving] using h

theorem squared_lambda_improved_le_18040536 :
    Code.Lambda
      (Code.interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)))
      ImprovedRadius ≤ 18040536 := by
  have h := lambda_interleaved_profile_le
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))
    IRSProfile.minDistance 2 1734 (by norm_num) irs_lambda_improved_le_1734
  convert h using 1 <;> norm_num

end ProximityPrize.SubmissionLower
