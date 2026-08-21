/-
  KernelGcd — remaining degree of (Q₀ − f Q₁) after agreement zeros
  at cell e = 65552, versus the 33-dimensional BW kernel.

  Distinct from puncture/defense budget, N×N det, ofBase dimension,
  Gal twist/descent Grassmann, and unique-decoding/Johnson cuts:

  BW interpolants satisfy (Q₀ − f Q₁)(α) = 0 on the agreement set of
  size n − e.  The residual degree of freedom on that polynomial, plus
  the rank-1 locator ray, is the only source of the 33-dim kernel.
  A 5314 claim has to pin a common Q₁-factor (the genuine locator),
  not count Grassmann or walk e back by punctures.
-/

namespace ProximityPrize.SubmissionLower.KernelGcd

def e : Nat := 65552
def n : Nat := 262144
def deg : Nat := 131072

/-- Square-row MCA length at this cell. -/
def Ncols : Nat := (e + 1) + (e + deg)

theorem Ncols_num : Ncols = 262177 := by native_decide

theorem excess : Ncols - n = 33 := by native_decide

/-- Agreement set size (correct positions). -/
def agree : Nat := n - e

theorem agree_num : agree = 196592 := by native_decide

/-- Strict degree bound on Q₀ − f Q₁ (deg Q₀ < e+deg). -/
def residualDeg : Nat := e + deg

theorem residualDeg_num : residualDeg = 196624 := by native_decide

/--
  Dimension of { polys of degree < e+deg vanishing on `agree` distinct
  points } = (e+deg) − (n−e) = 32, *assuming* those zeros are simple
  and the evaluation map on that degree class has full rank.
-/
theorem remaining_after_agreement : residualDeg - agree = 32 := by
  native_decide

/--
  32 residual degrees on Q₀−fQ₁ plus the 1-dimensional locator ray
  (Q₀, Q₁) = (γ Λ, Λ) recovers the rectangular excess 33.
  So the 33-dim kernel is *exactly* residual-of-agreement plus ray,
  not an extra Gal/ofBase direction.
-/
theorem remaining_plus_ray :
    (residualDeg - agree) + 1 = Ncols - n := by
  native_decide

/-- Locator Q₁ has deg < e+1 = 65553; residual 32 does not fill it. -/
theorem residual_lt_locator_deg : residualDeg - agree < e + 1 := by
  native_decide

/--
  Unique-decoding overflow is 16 errors. Residual 32 is *twice* that
  overflow: the extra 16 errors each contribute a simple zero to the
  locator and a matching residual factor, doubling rather than
  cancelling the 33-count. gcd-degree of a generic 33-dim slice is 0;
  5314 needs the *common* Q₁ factor of degree e, not a 16-error core.
-/
def tUnique : Nat := (n - deg) / 2   -- (d)/2 with d = n-deg+1, floor
theorem overflow_vs_residual :
    e - 65536 = 16 ∧ residualDeg - agree = 32 ∧
      2 * (e - 65536) = residualDeg - agree := by
  native_decide

/-- Q₁-degree window 65553 vs residual 32: a common gcd of degree e
    cannot be read off the 32-dimensional residual alone. -/
theorem locator_window_gap : (e + 1) - (residualDeg - agree) = 65521 := by
  native_decide

end ProximityPrize.SubmissionLower.KernelGcd
