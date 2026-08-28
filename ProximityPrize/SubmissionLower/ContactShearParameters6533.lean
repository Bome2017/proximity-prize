import ProximityPrize.SubmissionLower.ContactParameters6533

/-!
# Exact arithmetic for the conservative 65.56-bit separable-shear ledger

This research module combines the proved sharp `Y` recurrence cap with the
full conservative cost of replacing a bad `R` projection by the sheared
parameter `S = R + Z`.

For a curve component of degree vector `g` and an agreement cut of cap `E`,
the unchanged-coordinate zero count costs

`E.y * dY + E.r * dR + E.z * dZ`.

After the shear, `deg_S E <= E.r`, `deg_Z E <= E.z + E.r`, and the summed
`S`-degree is bounded by the old `R`- and `Z`-degree budgets.  Thus the
conservative replacement costs exactly one old mixed term plus

`2 * E.r * dZ`.

The theorems below check that charging this correction on every regular
component still leaves strict room below the alignment budget.  They prove
only closed arithmetic; the field-theoretic separable-shear lemma and its
geometric integration remain separate obligations.
-/

namespace ProximityPrize.SubmissionLower.ContactShearParameters6533

open ContactParameters6533

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Sharp recurrence vector: `2*yCap` is replaced by `2*yCap - 1`. -/
def sharpTailVector (h : ℕ) : DegreeVector :=
  ⟨1 + h * (2 * yCap - 1),
    h * (2 * slopeCap - 1),
    2 * h * seedTotalCap⟩

def sharpFirstTail : DegreeVector := sharpTailVector (w + 1)

def sharpAgreement : DegreeVector :=
  ⟨1 + w * (2 * yCap - 1),
    w * (2 * slopeCap - 1),
    2 * w * seedTotalCap + 1⟩

def sharpRefinedFirstProjection : ℕ :=
  sharpFirstTail.y * seedTotalCap + yCap * firstTailSeedTotal -
    yCap * sharpFirstTail.y

def sharpRefinedAgreementProjection : ℕ :=
  sharpAgreement.y * seedTotalCap + yCap * agreementSeedTotal -
    yCap * sharpAgreement.y

/-- The old `Z` projection budget, with the sharp agreement cut. -/
def sharpAgreementZProjection : ℕ :=
  mixed surfaceVector sharpAgreement unitZ

/-- The old `Y` projection budget.  Like the Z budget, it is strictly
below the characteristic, so a transcendental Y projection cannot be
inseparable. -/
def sharpAgreementYProjection : ℕ :=
  mixed surfaceVector sharpAgreement unitY

/-- A conservative summed degree budget for `S = R + Z`. -/
def sharpAgreementSProjection : ℕ :=
  sharpRefinedAgreementProjection + sharpAgreementZProjection

/-- The regular whole-surface ledger with the sharp agreement vector but
before paying for the shear. -/
def sharpYWholeNumerator : ℕ :=
  (n - w) ^ 2 * mixed surfaceVector sharpAgreement sharpAgreement +
    (errors + 1) * (n - w) * gap *
      mixed surfaceVector sharpAgreement unitZ

/-- Extra mixed-degree cost `2 * E.r * dZ` before incidence scaling. -/
def shearMixedPenalty : ℕ :=
  2 * sharpAgreement.r * sharpAgreementZProjection

/-- The regular-ledger numerator pays the shear cost on every proper node. -/
def shearWholePenalty : ℕ := (n - w) ^ 2 * shearMixedPenalty

def sharpYTotalNumerator : ℕ :=
  sharpYWholeNumerator + gap * sharpSingularNumerator

def shearedTotalNumerator : ℕ :=
  sharpYTotalNumerator + shearWholePenalty

def sharpYLedgerCeiling : ℕ :=
  (sharpYTotalNumerator + gapSquared - 1) / gapSquared

def shearedLedgerCeiling : ℕ :=
  (shearedTotalNumerator + gapSquared - 1) / gapSquared

theorem sharp_vector_values :
    sharpFirstTail = ⟨7471105, 1179648, 104595456⟩ ∧
      sharpAgreement = ⟨7471048, 1179639, 104594659⟩ := by
  norm_num [sharpFirstTail, sharpTailVector, sharpAgreement, yCap,
    ContactParameters6533.weightedCap, ContactParameters6533.multiplicity,
    ContactParameters6533.agreements, ContactParameters6533.n,
    ContactParameters6533.errors, ContactParameters6533.w,
    ContactParameters6533.slopeCap, ContactParameters6533.seedTotalCap]

theorem sharp_projection_values :
    sharpRefinedFirstProjection = 5797577103 ∧
      sharpRefinedAgreementProjection = 5797532871 ∧
      sharpAgreementZProjection = 71564771 ∧
      sharpAgreementSProjection = 5869097642 := by
  norm_num [sharpRefinedFirstProjection, sharpRefinedAgreementProjection,
    sharpAgreementZProjection, sharpAgreementSProjection, sharpFirstTail,
    sharpTailVector, sharpAgreement, firstTailSeedTotal,
    agreementSeedTotal, surfaceVector, unitZ, mixed, yCap,
    ContactParameters6533.weightedCap,
    ContactParameters6533.multiplicity, ContactParameters6533.agreements,
    ContactParameters6533.n, ContactParameters6533.errors,
    ContactParameters6533.w, ContactParameters6533.slopeCap,
    ContactParameters6533.seedTotalCap]

theorem transverse_projection_values :
    sharpAgreementYProjection = 993649256 ∧
      sharpAgreementZProjection = 71564771 := by
  norm_num [sharpAgreementYProjection, sharpAgreementZProjection,
    surfaceVector, sharpAgreement, unitY, unitZ, mixed, yCap,
    ContactParameters6533.weightedCap,
    ContactParameters6533.multiplicity, ContactParameters6533.agreements,
    ContactParameters6533.n, ContactParameters6533.errors,
    ContactParameters6533.w, ContactParameters6533.slopeCap,
    ContactParameters6533.seedTotalCap]

/-- Both coordinates left unchanged by the R/Z shear have full family
degree budget below the characteristic.  Therefore every nonconstant
projection to either coordinate is automatically separable. -/
theorem transverse_projection_budgets_below_characteristic :
    sharpAgreementYProjection < prime ∧
      sharpAgreementZProjection < prime := by
  rw [transverse_projection_values.1, transverse_projection_values.2]
  norm_num [prime]

theorem sharp_y_whole_exact :
    sharpYWholeNumerator = 378061272418177601723497746 := by
  norm_num [sharpYWholeNumerator, surfaceVector, sharpAgreement, unitZ,
    mixed, yCap, ContactParameters6533.weightedCap,
    ContactParameters6533.multiplicity, ContactParameters6533.agreements,
    ContactParameters6533.n, ContactParameters6533.errors,
    ContactParameters6533.w, gap, ContactParameters6533.slopeCap,
    ContactParameters6533.seedTotalCap]

theorem sharp_y_total_exact :
    sharpYTotalNumerator = 378617935056849171941877686 := by
  rw [show sharpYTotalNumerator =
      sharpYWholeNumerator + gap * sharpSingularNumerator by rfl,
    sharp_y_whole_exact, ContactParameters6533.sharp_singular_exact]
  norm_num [gap, ContactParameters6533.agreements, ContactParameters6533.n,
    ContactParameters6533.errors, ContactParameters6533.w]

theorem sharp_y_ledger_ceiling_exact :
    sharpYLedgerCeiling = 136171317650030746 := by
  norm_num [sharpYLedgerCeiling, sharp_y_total_exact,
    ContactParameters6533.gap_squared_exact]

theorem sharp_y_budget_slack :
    alignmentBudget - sharpYLedgerCeiling = 1319046405666797 := by
  rw [sharp_y_ledger_ceiling_exact]
  norm_num [alignmentBudget]

theorem shear_penalty_values :
    shearMixedPenalty = 168841189795338 ∧
      shearWholePenalty = 2900713814428521471944202 := by
  norm_num [shearMixedPenalty, shearWholePenalty, sharpAgreement,
    sharpAgreementZProjection, surfaceVector, unitZ, mixed, yCap,
    ContactParameters6533.weightedCap, ContactParameters6533.multiplicity,
    ContactParameters6533.agreements, ContactParameters6533.n,
    ContactParameters6533.errors, ContactParameters6533.w,
    ContactParameters6533.slopeCap, ContactParameters6533.seedTotalCap]

theorem sheared_total_exact :
    shearedTotalNumerator = 381518648871277693413821888 := by
  rw [show shearedTotalNumerator = sharpYTotalNumerator + shearWholePenalty by rfl,
    sharp_y_total_exact, shear_penalty_values.2]

theorem sheared_ledger_ceiling_exact :
    shearedLedgerCeiling = 137214569925380752 := by
  norm_num [shearedLedgerCeiling, sheared_total_exact,
    ContactParameters6533.gap_squared_exact]

theorem sheared_budget_slack :
    alignmentBudget - shearedLedgerCeiling = 275794130316791 := by
  rw [sheared_ledger_ceiling_exact]
  norm_num [alignmentBudget]

/-- The conservative full shear correction still fits strictly below the
65.56-bit alignment budget. -/
theorem sheared_strict_budget :
    shearedTotalNumerator < alignmentBudget * gapSquared := by
  rw [sheared_total_exact, ContactParameters6533.gap_squared_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactShearParameters6533

#print axioms ProximityPrize.SubmissionLower.ContactShearParameters6533.sharp_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactShearParameters6533.transverse_projection_budgets_below_characteristic
#print axioms ProximityPrize.SubmissionLower.ContactShearParameters6533.sharp_y_total_exact
#print axioms ProximityPrize.SubmissionLower.ContactShearParameters6533.shear_penalty_values
#print axioms ProximityPrize.SubmissionLower.ContactShearParameters6533.sheared_strict_budget
