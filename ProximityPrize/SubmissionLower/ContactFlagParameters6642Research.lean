import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6642Research

/-!
# Exact flag-complete interpolation parameters for score 66.42

The coefficient and local-rank sums are stated directly from the nested
support `R <= s`, `Y+R <= M`, `Y+R+Z <= L`.  This file is arithmetic only;
the generic flag-rank kernel is a separate geometric interface.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagParameters6642Research

open Finset

set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 137490364055697543

def errors : ℕ := 79194
def agreements : ℕ := n - errors
def multiplicity : ℕ := 29
def totalCap : ℕ := 617
def slopeCap : ℕ := 8
def weightedCap : ℕ := multiplicity * agreements
def middleCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * totalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

/-- Number of monomials in the strict weighted, flag-complete box. -/
def coefficientCount : ℕ :=
  ContactFlagInterpolation6642Research.coefficientCount
    weightedCap w middleCap totalCap slopeCap

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

def localBoxCount (M L s : ℕ) : ℕ :=
  ∑ i ∈ range (M + 1),
    ∑ j ∈ range (s + 1), (L + 1 - i - j)

/-- The translated contact ideal contributes no shifted box when its contact
exponent exceeds any one of the three nested caps.  Writing this guard
explicitly avoids interpreting a negative cap by truncated natural-number
subtraction. -/
def shiftedLocalBoxCount (r : ℕ) : ℕ :=
  let h := contactExponent r
  let Mr := min r middleCap
  if h ≤ Mr ∧ h ≤ totalCap ∧ h ≤ slopeCap then
    localBoxCount (Mr - h) (totalCap - h) (slopeCap - h)
  else 0

/-- Exact rank bound of one translated flag-complete contact block. -/
def localContactRank : ℕ :=
  ContactFlagRankKernel6642Research.localRankBound
    multiplicity middleCap totalCap slopeCap

def totalContactRank : ℕ := n * localContactRank
def rankMargin : ℕ := coefficientCount - totalContactRank

theorem parameter_values :
    agreements = 182950 ∧ weightedCap = 5305550 ∧ middleCap = 40 ∧
    gap = 51879 ∧ algebraicCap = 9255 ∧
    implicitWeightedCap = 79583250 ∧ implicitYCap = 607 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, middleCap, w,
    gap, algebraicCap, slopeCap, totalCap, implicitWeightedCap, implicitYCap]

theorem coefficient_count_exact : coefficientCount = 488225286738 := by
  norm_num [coefficientCount,
    ContactFlagInterpolation6642Research.coefficientCount, middleCap,
    totalCap, slopeCap, weightedCap, multiplicity, agreements, n, errors, w,
    Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 1862430 := by
  norm_num [localContactRank,
    ContactFlagRankKernel6642Research.localRankBound,
    ContactFlagRankKernel6642Research.contactRankBound,
    ContactFlagRankKernel6642Research.blockInputCount,
    ContactFlagRankKernel6642Research.blockKernelLowerBound,
    contactExponent, multiplicity, middleCap, weightedCap, agreements, n,
    errors, w, totalCap, slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 488224849920 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 436818 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem characteristic_gates :
    weightedCap < prime ∧ implicitWeightedCap < prime ∧
      algebraicCap < prime ∧ slopeCap < prime := by
  norm_num [weightedCap, multiplicity, agreements, n, errors,
    implicitWeightedCap, algebraicCap, slopeCap, totalCap, prime]

end ProximityPrize.SubmissionLower.ContactFlagParameters6642Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagParameters6642Research.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactFlagParameters6642Research.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactFlagParameters6642Research.rank_margin_exact
#print axioms ProximityPrize.SubmissionLower.ContactFlagParameters6642Research.interpolation_gate
