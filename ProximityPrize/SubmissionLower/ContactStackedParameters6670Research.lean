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
def agreements : ℕ := 182399
def errors : ℕ := n - agreements
def gap : ℕ := agreements - w

/-- The three profiles are `(multiplicity, seed cap, slope cap)`. -/
structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨60, 943, 18⟩
def profileB : Profile := ⟨35, 3393, 9⟩
def profileC : Profile := ⟨31, 216672, 9⟩

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
    errors = 79745 ∧ gap = 51328 := by
  norm_num [errors, gap, n, agreements, w]

theorem profileA_coefficients_exact :
    profileA.coefficients = 6472120695650 := by
  change coefficientCount (60 * 182399) 131071 943 18 = 6472120695650
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (60 * 182399) 131071 943 18 84 (by norm_num) (by norm_num)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 24689056 := by
  change localRankBound 60 943 18 = 24689056
  decide

theorem profileA_values :
    profileA.weightedCap = 10943940 ∧ profileA.yCap = 83 ∧
      profileA.localRank = 24689056 ∧
      profileA.coefficients = 6472120695650 ∧
      profileA.nullity = 32799586 := by
  refine ⟨by norm_num [Profile.weightedCap, profileA, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileA, agreements, w],
    profileA_localRank_exact, profileA_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact,
    profileA_localRank_exact]
  norm_num [n]

theorem profileB_coefficients_exact :
    profileB.coefficients = 4444681710810 := by
  change coefficientCount (35 * 182399) 131071 3393 9 = 4444681710810
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (35 * 182399) 131071 3393 9 49 (by norm_num) (by norm_num)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 16955115 := by
  change localRankBound 35 3393 9 = 16955115
  decide

theorem profileB_values :
    profileB.weightedCap = 6383965 ∧ profileB.yCap = 48 ∧
      profileB.localRank = 16955115 ∧
      profileB.coefficients = 4444681710810 ∧
      profileB.nullity = 44250 := by
  refine ⟨by norm_num [Profile.weightedCap, profileB, agreements],
    by norm_num [Profile.yCap, Profile.weightedCap, profileB, agreements, w],
    profileB_localRank_exact, profileB_coefficients_exact, ?_⟩
  rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact,
    profileB_localRank_exact]
  norm_num [n]

theorem profileC_coefficients_exact :
    profileC.coefficients = 218669686467540 := by
  change coefficientCount (31 * 182399) 131071 216672 9 = 218669686467540
  rw [ContactStackedParameters6656Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (31 * 182399) 131071 216672 9 44 (by norm_num) (by norm_num)]
  decide

theorem profileC_localRank_exact : profileC.localRank = 834158655 := by
  change localRankBound 31 216672 9 = 834158655
  decide

theorem profileC_values :
    profileC.weightedCap = 5654369 ∧ profileC.yCap = 43 ∧
      profileC.localRank = 834158655 ∧
      profileC.coefficients = 218669686467540 ∧
      profileC.nullity = 11220 := by
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
        min profileA.slopeCap profileB.slopeCap) = (35, 943, 9) ∧
      (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
        min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
        min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap) =
          (31, 943, 9) := by
  norm_num [profileA, profileB, profileC]

end ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
