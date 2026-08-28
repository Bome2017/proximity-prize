import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Exact interpolation profiles for the stacked 66.96 candidate

This module certifies the three ordinary differential-contact kernels used by
the bounded active-YZ recursive-GCD construction at `a = 182414`.  It reuses
the weighted-cutoff reduction proved for the 66.56 parameter certificate; only
the target-specific natural-number arithmetic is new here.

No GCD decomposition, residual ledger, or decoding claim is made in this
arithmetic module.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

open ContactInterpolation ContactRankKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def agreements : ℕ := 182376
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨32, 12659, 9⟩
def profileB : Profile := ⟨40, 1521, 11⟩
def profileC : Profile := ⟨63, 970, 19⟩

namespace Profile

def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def characteristicCap (P : Profile) : ℕ :=
  (2 * P.slopeCap - 1) * P.weightedCap

def coefficients (P : Profile) : ℕ :=
  coefficientCount P.weightedCap w P.seedCap P.slopeCap

def localRank (P : Profile) : ℕ :=
  localRankBound P.multiplicity P.seedCap P.slopeCap

def totalRank (P : Profile) : ℕ := n * P.localRank
def nullity (P : Profile) : ℕ := P.coefficients - P.totalRank

end Profile

theorem base_values :
    errors = 79768 ∧ gap = 51305 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 13680357114120 := by
  change coefficientCount (32 * 182376) 131071 12659 9 = 13680357114120
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (32 * 182376) 131071 12659 9 45 (by norm_num) (by norm_num)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 52186420 := by
  change localRankBound 32 12659 9 = 52186420
  decide

theorem profileA_values :
    profileA.weightedCap = 5836032 ∧ profileA.yCap = 44 ∧
      profileA.localRank = 52186420 ∧
      profileA.coefficients = 13680357114120 ∧
      profileA.nullity = 229640 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 3052221594090 := by
  change coefficientCount (40 * 182376) 131071 1521 11 = 3052221594090
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (40 * 182376) 131071 1521 11 56 (by norm_num) (by norm_num)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 11643292 := by
  change localRankBound 40 1521 11 = 11643292
  decide

theorem profileB_values :
    profileB.weightedCap = 7295040 ∧ profileB.yCap = 55 ∧
      profileB.localRank = 11643292 ∧
      profileB.coefficients = 3052221594090 ∧
      profileB.nullity = 2456042 := by
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    profileB_localRank_exact, profileB_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 7704991793900 := by
  change coefficientCount (63 * 182376) 131071 970 19 = 7704991793900
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (63 * 182376) 131071 970 19 88 (by norm_num) (by norm_num)]
  decide

theorem profileC_localRank_exact : profileC.localRank = 29392190 := by
  change localRankBound 63 970 19 = 29392190
  decide

theorem profileC_values :
    profileC.weightedCap = 11489688 ∧ profileC.yCap = 87 ∧
      profileC.localRank = 29392190 ∧
      profileC.coefficients = 7704991793900 ∧
      profileC.nullity = 5538540 := by
  refine ⟨by norm_num [Profile.weightedCap, profileC, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileC, agreements, w],
    profileC_localRank_exact, profileC_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileC_coefficients_exact,
    profileC_localRank_exact]
  norm_num [n]

/-- Each of the three constraint maps has a nonzero kernel. -/
theorem interpolation_gates :
      profileA.totalRank < profileA.coefficients ∧
      profileB.totalRank < profileB.coefficients ∧
      profileC.totalRank < profileC.coefficients := by
  simp only [Profile.totalRank]
  rw [profileA_coefficients_exact, profileA_localRank_exact,
    profileB_coefficients_exact, profileB_localRank_exact,
    profileC_coefficients_exact, profileC_localRank_exact]
  norm_num [n]

/-- The ordinary derivative and coefficient arithmetic stays below the
challenge-field characteristic. -/
theorem characteristic_gates :
    profileA.characteristicCap < prime ∧
      (2 * profileA.slopeCap - 1) * profileA.seedCap < prime ∧
      profileA.slopeCap < prime ∧
    profileB.characteristicCap < prime ∧
      (2 * profileB.slopeCap - 1) * profileB.seedCap < prime ∧
      profileB.slopeCap < prime ∧
    profileC.characteristicCap < prime ∧
      (2 * profileC.slopeCap - 1) * profileC.seedCap < prime ∧
      profileC.slopeCap < prime := by
  norm_num [Profile.characteristicCap, Profile.weightedCap, profileA, profileB,
    profileC, agreements, prime]

/-- Coordinatewise caps inherited by the first GCD and the final common
divisor, respectively. -/
theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
        min profileA.seedCap profileB.seedCap,
        min profileA.slopeCap profileB.slopeCap) = (32, 1521, 9) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (32, 970, 9) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
