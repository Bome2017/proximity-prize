import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic for the 65.33-bit direct-contact candidate

This module records the `e = 78117`, `m = 19`, `L = 325`, `s = 5` row of
the sharp-incidence, no-projection-gate structural audit.  It proves only
closed arithmetic facts.  In particular, `projection_gate_fails` makes
explicit that this row cannot be integrated through the existing coordinate
or joint-Newton projection characteristic gate.

All certificates are checked by the Lean kernel.  No native-decision axiom is
used.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6533

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 100000000000000000

def errors : ℕ := 78117
def agreements : ℕ := n - errors
def multiplicity : ℕ := 19
def seedTotalCap : ℕ := 325
def slopeCap : ℕ := 5
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap

/-- Nat subtraction is the positive part of each strict coefficient cap. -/
def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

/-- Exact rank of the translated order-`multiplicity` contact block at one
evaluation coordinate. -/
def localContactRank : ℕ :=
  ∑ r ∈ range multiplicity,
    (((slopeCap + 1) *
        (∑ f ∈ range (min r seedTotalCap + 1),
          (seedTotalCap + 1 - f))) -
      ((slopeCap + 1 - contactExponent r) *
        (∑ f ∈ range (min r seedTotalCap + 1 - contactExponent r),
          (seedTotalCap + 1 - contactExponent r - f))))

def totalContactRank : ℕ := n * localContactRank
def rankMargin : ℕ := coefficientCount - totalContactRank

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

/-- The coefficient of the product of three distinct hyperplane classes. -/
def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitY : DegreeVector := ⟨1, 0, 0⟩
def unitR : DegreeVector := ⟨0, 1, 0⟩
def unitZ : DegreeVector := ⟨0, 0, 1⟩

def surfaceVector : DegreeVector := ⟨yCap, slopeCap, seedTotalCap⟩

def tailVector (h : ℕ) : DegreeVector :=
  ⟨1 + 2 * h * yCap,
    h * (2 * slopeCap - 1),
    2 * h * seedTotalCap⟩

def firstTail : DegreeVector := tailVector (w + 1)
def agreementVector : DegreeVector :=
  ⟨1 + 2 * w * yCap,
    w * (2 * slopeCap - 1),
    2 * w * seedTotalCap + 1⟩

/-- The old rectangular coordinate-projection maximum. -/
def projectionMax : ℕ :=
  max (mixed surfaceVector firstTail unitY)
    (max (mixed surfaceVector agreementVector unitY)
      (max (mixed surfaceVector firstTail unitR)
        (max (mixed surfaceVector agreementVector unitR)
          (max (mixed surfaceVector firstTail unitZ)
            (mixed surfaceVector agreementVector unitZ)))))

def firstTailSeedTotal : ℕ := 1 + 2 * (w + 1) * seedTotalCap
def agreementSeedTotal : ℕ := 1 + 2 * w * seedTotalCap

/-- Joint `(Y,Z)` Newton/Sylvester bounds after eliminating `Y`. -/
def refinedFirstProjection : ℕ :=
  firstTail.y * seedTotalCap + yCap * firstTailSeedTotal - yCap * firstTail.y

def refinedAgreementProjection : ℕ :=
  agreementVector.y * seedTotalCap + yCap * agreementSeedTotal -
    yCap * agreementVector.y

def refinedProjectionMax : ℕ :=
  max (mixed surfaceVector firstTail unitY)
    (max (mixed surfaceVector agreementVector unitY)
      (max refinedFirstProjection
        (max refinedAgreementProjection
          (max (mixed surfaceVector firstTail unitZ)
            (mixed surfaceVector agreementVector unitZ)))))

def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w
def implicitProjectionMax : ℕ :=
  max algebraicCap (max (2 * implicitYCap * algebraicCap) implicitYCap)

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

/-- Sharp whole-surface numerator over the common denominator `gap^2`. -/
def sharpWholeNumerator : ℕ :=
  (n - w) ^ 2 * mixed surfaceVector agreementVector agreementVector +
  (errors + 1) * (n - w) * gap *
    mixed surfaceVector agreementVector unitZ

/-- Sharp singular-branch numerator over the denominator `gap`. -/
def sharpSingularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      mixed liftedSurface implicitCut liftedLast +
      (errors + 1) * mixed liftedSurface implicitCut unitZ) +
    (n - w) * mixed liftedSurface implicitCut liftedAgreement

def sharpTotalNumerator : ℕ :=
  sharpWholeNumerator + gap * sharpSingularNumerator

def gapSquared : ℕ := gap ^ 2
def sharpLedgerCeiling : ℕ :=
  (sharpTotalNumerator + gapSquared - 1) / gapSquared

theorem parameter_values :
    agreements = 184027 ∧ weightedCap = 3496513 ∧ yCap = 26 ∧
    gap = 52956 ∧ algebraicCap = 2925 ∧
    implicitWeightedCap = 31468617 ∧ implicitYCap = 240 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 76548187338 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 292005 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 76547358720 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 828618 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem projection_values :
    projectionMax = 4430233925 ∧
    refinedProjectionMax = 4253024581 ∧
    implicitProjectionMax = 1404000 := by
  norm_num [projectionMax, refinedProjectionMax, refinedFirstProjection,
    refinedAgreementProjection, surfaceVector, firstTail, tailVector,
    agreementVector, firstTailSeedTotal, agreementSeedTotal, unitY, unitR,
    unitZ, mixed, yCap, weightedCap, multiplicity, agreements, n, errors, w,
    seedTotalCap, slopeCap, implicitProjectionMax, implicitYCap,
    implicitWeightedCap, algebraicCap]

/-- This candidate deliberately lies beyond both existing regular projection
gates, so removing that gate is a theorem-level requirement, not a retune. -/
theorem projection_gate_fails : prime ≤ refinedProjectionMax := by
  rw [projection_values.2.1]
  norm_num [prime]

theorem implicit_characteristic_gates :
    implicitWeightedCap < prime ∧ implicitProjectionMax < prime ∧
    algebraicCap < prime ∧ slopeCap < prime := by
  rw [parameter_values.2.2.2.2.2.1, projection_values.2.2]
  norm_num [prime, algebraicCap, slopeCap, seedTotalCap]

theorem sharp_whole_exact :
    sharpWholeNumerator = 279363116032635977989204968 := by
  norm_num [sharpWholeNumerator, surfaceVector, agreementVector, unitZ, mixed,
    yCap, weightedCap, multiplicity, slopeCap, seedTotalCap, w, n, errors,
    gap, agreements]

theorem sharp_singular_exact :
    sharpSingularNumerator = 7091459677463447565 := by
  norm_num [sharpSingularNumerator, liftedSurface, implicitCut, liftedLast,
    liftedAgreement, unitZ, mixed, implicitYCap, implicitWeightedCap,
    algebraicCap, yCap, weightedCap, multiplicity, agreements, n, errors, w,
    gap, slopeCap, seedTotalCap]

theorem sharp_total_exact :
    sharpTotalNumerator = 279738651371315732318457108 := by
  rw [show sharpTotalNumerator =
      sharpWholeNumerator + gap * sharpSingularNumerator by rfl,
    sharp_whole_exact, sharp_singular_exact]
  norm_num [gap, agreements, n, errors, w]

theorem gap_squared_exact : gapSquared = 2804337936 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

theorem sharp_division_certificate :
    sharpTotalNumerator =
        99752118951228897 * gapSquared + 2641920516 ∧
      2641920516 < gapSquared := by
  rw [sharp_total_exact, gap_squared_exact]
  norm_num

theorem sharp_ledger_ceiling_exact :
    sharpLedgerCeiling = 99752118951228898 := by
  norm_num [sharpLedgerCeiling, sharp_total_exact, gap_squared_exact]

theorem sharp_ledger_budget_slack :
    alignmentBudget - sharpLedgerCeiling = 247881048771102 := by
  rw [sharp_ledger_ceiling_exact]
  norm_num [alignmentBudget]

theorem sharp_strict_budget :
    sharpTotalNumerator < alignmentBudget * gapSquared := by
  rw [sharp_total_exact, gap_squared_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactParameters6533

#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.projection_gate_fails
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.sharp_total_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.sharp_division_certificate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6533.sharp_strict_budget
