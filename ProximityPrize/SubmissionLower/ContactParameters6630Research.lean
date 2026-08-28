import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagParameters6642Research

/-!
# Exact downstream parameters for the 66.42 row

The historical namespace is retained so the established adaptive residual
pipeline can be reused without duplicating it.  Every scalar is an alias of
the independently checked flag-complete row `(errors,m,s,L)=(79194,29,8,617)`.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6630Research

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := ContactFlagParameters6642Research.n
def w : ℕ := ContactFlagParameters6642Research.w
def prime : ℕ := ContactFlagParameters6642Research.prime
def alignmentBudget : ℕ := ContactFlagParameters6642Research.alignmentBudget

def errors : ℕ := ContactFlagParameters6642Research.errors
def agreements : ℕ := ContactFlagParameters6642Research.agreements
def multiplicity : ℕ := ContactFlagParameters6642Research.multiplicity
def seedTotalCap : ℕ := ContactFlagParameters6642Research.totalCap
def slopeCap : ℕ := ContactFlagParameters6642Research.slopeCap
def weightedCap : ℕ := ContactFlagParameters6642Research.weightedCap
def yCap : ℕ := ContactFlagParameters6642Research.middleCap
def gap : ℕ := ContactFlagParameters6642Research.gap
def algebraicCap : ℕ := ContactFlagParameters6642Research.algebraicCap
def implicitWeightedCap : ℕ := ContactFlagParameters6642Research.implicitWeightedCap
def implicitYCap : ℕ := ContactFlagParameters6642Research.implicitYCap

/-- Number of monomials in the strict weighted interpolation box. -/
def coefficientCount : ℕ :=
  ContactFlagParameters6642Research.coefficientCount

def contactExponent (r : ℕ) : ℕ :=
  ContactFlagParameters6642Research.contactExponent r

/-- Exact rank bound of one translated order-`multiplicity` contact block. -/
def localContactRank : ℕ :=
  ContactFlagParameters6642Research.localContactRank

def totalContactRank : ℕ := n * localContactRank
def rankMargin : ℕ := coefficientCount - totalContactRank

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitZ : DegreeVector := ⟨0, 0, 1⟩
def liftedSurface : DegreeVector := ⟨implicitYCap, 1, algebraicCap⟩
def implicitCut : DegreeVector := ⟨implicitYCap, 0, algebraicCap⟩
def liftedLast : DegreeVector :=
  ⟨1 + 2 * implicitWeightedCap * implicitYCap,
    implicitWeightedCap,
    2 * implicitWeightedCap * algebraicCap⟩
def liftedAgreement : DegreeVector :=
  ⟨1 + 2 * w * implicitYCap,
    w,
    2 * w * algebraicCap + 1⟩

theorem parameter_values :
    agreements = 182950 ∧ weightedCap = 5305550 ∧ yCap = 40 ∧
    gap = 51879 ∧ algebraicCap = 9255 ∧
    implicitWeightedCap = 79583250 ∧ implicitYCap = 607 := by
  simpa [agreements, weightedCap, yCap, gap, algebraicCap,
    implicitWeightedCap, implicitYCap] using
      ContactFlagParameters6642Research.parameter_values

theorem coefficient_count_exact : coefficientCount = 488225286738 := by
  simpa [coefficientCount] using
    ContactFlagParameters6642Research.coefficient_count_exact

theorem local_contact_rank_exact : localContactRank = 1862430 := by
  simpa [localContactRank] using
    ContactFlagParameters6642Research.local_contact_rank_exact

theorem total_contact_rank_exact : totalContactRank = 488224849920 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n, ContactFlagParameters6642Research.n]

theorem rank_margin_exact : rankMargin = 436818 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem characteristic_gates :
    weightedCap < prime ∧ implicitWeightedCap < prime ∧
      algebraicCap < prime ∧ slopeCap < prime := by
  simpa [weightedCap, implicitWeightedCap, algebraicCap, slopeCap, prime] using
    ContactFlagParameters6642Research.characteristic_gates

end ProximityPrize.SubmissionLower.ContactParameters6630Research

#print axioms ProximityPrize.SubmissionLower.ContactParameters6630Research.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6630Research.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6630Research.rank_margin_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6630Research.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6630Research.characteristic_gates
