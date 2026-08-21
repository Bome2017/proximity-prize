import ProximityPrize.SubmissionLower.FiniteTaylorFactorQBridge
import ProximityPrize.SubmissionLower.Cap72FactorAudit

namespace ProximityPrize.SubmissionLower.FiniteTaylorCapFactorHeight

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.FiniteTaylorCore
open ProximityPrize.SubmissionLower.Cap72FactorAudit

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

/-- The Cap72 `(Z,Y)` grading gives the uniform coefficient-height premise
needed by integral scaling and Taylor forcing. -/
theorem factor_coeff_polyHeight_le_seventyTwo
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) (j : ℕ) :
    polyHeight (R.coeff j) ≤ 72 := by
  have htotal := factor_totalDegree_swapZX_le Q hR hR0
  have hcoeff : ((swapZX R).coeff j).natDegree ≤ 72 := by
    by_cases hz : (swapZX R).coeff j = 0
    · simp [hz]
    · have hmem : j ∈ (swapZX R).support :=
        Polynomial.mem_support_iff.mpr hz
      have hc := Polynomial.Bivariate.coeff_totalDegree_le
        (swapZX R) hmem
      omega
  have hswap : (swapZX R).coeff j =
      Polynomial.Bivariate.swap (R.coeff j) := by
    simp [swapZX]
  rw [hswap] at hcoeff
  change Polynomial.Bivariate.natDegreeY
    (Polynomial.Bivariate.swap (R.coeff j)) ≤ 72 at hcoeff
  rw [Polynomial.Bivariate.natDegreeY_swap] at hcoeff
  exact hcoeff

end

end ProximityPrize.SubmissionLower.FiniteTaylorCapFactorHeight
