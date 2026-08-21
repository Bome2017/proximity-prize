import ProximityPrize.SubmissionLower.AlignmentFromPolynomials
import ProximityPrize.SubmissionLower.Target5314Alignment
import ProximityPrize.SubmissionLower.Target5314TaylorEndpoint

/-!
# Complete 53.14 selected-polynomial alignment

This file performs the final branch composition.  The two nested filters
returned by the Cap72 factor selection supply exactly the two root identities
needed by the concrete Taylor endpoint; the endpoint is then consumed by the
finite-resultant alignment theorem.
-/

namespace ProximityPrize.SubmissionLower.Target5314FullAlignment

open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open Cap72BadRoots5314 Cap72SecondBranch5314

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

/-- The complete algebraic extraction contract at the 53.14 target. -/
theorem hasLargeSelectedPolynomialAlignment5314 :
    HasLargeSelectedPolynomialAlignment := by
  classical
  intro rows bad _hbad selected hcard
  obtain ⟨Q, R, hRmem, hRirr, hRpos, hRdeg, x₀, _hx₀, hdegree,
      hresultant, H, _hHmem, hHirr, hHpos, hHdeg, hHheight, hHdvd,
      _hPsep, _hHsep, hbranchCardRaw⟩ :=
    Cap72SecondBranch5314.exists_second_branch selected hcard
  let first : Finset IRSProfile.Field := bad.filter fun gamma =>
    Cap72FactorSelection.specializeAt gamma
      (selectedPolynomial selected gamma) R = 0
  let branch : Finset IRSProfile.Field := first.filter fun gamma =>
    SequentialFactorSelection.evalZY gamma
      ((selectedPolynomial selected gamma).eval x₀) H = 0
  have hbranchCard : FactorThreshold5314.branchThreshold < branch.card := by
    simpa only [branch, first] using hbranchCardRaw
  have hbranchSub : branch ⊆ bad := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hgamma).1).1
  have hbranchHroot : ∀ gamma ∈ branch,
      (FiniteTaylorExtraction.specializeZ gamma H).eval
        ((selectedPolynomial selected gamma).eval x₀) = 0 := by
    intro gamma hgamma
    have hroot := (Finset.mem_filter.mp hgamma).2
    simpa only [SequentialFactorSelection.evalZY,
      FiniteTaylorExtraction.specializeZ] using hroot
  have hbranchRroot : ∀ gamma ∈ branch,
      Polynomial.eval₂ (RingHom.id (Polynomial IRSProfile.Field))
        (selectedPolynomial selected gamma)
        (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom gamma))) = 0 := by
    intro gamma hgamma
    have hfirst : gamma ∈ first := (Finset.mem_filter.mp hgamma).1
    have hroot := (Finset.mem_filter.mp hfirst).2
    rw [Polynomial.eval₂_id]
    change Polynomial.eval (selectedPolynomial selected gamma)
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom gamma))) = 0 at hroot
    exact hroot
  have hRdvd : R ∣ Q.polynomial :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRmem
  have hR0 : R ≠ 0 := Irreducible.ne_zero hRirr
  have hPcoeff : ∀ i,
      ((SequentialFactorSelection.specializeX x₀ R).coeff i).natDegree ≤ 72 :=
    Target5314Alignment.specializedFactor_coeff_natDegree_le_seventyTwo
      Q R hRdvd hR0 x₀
  obtain ⟨data, hendpoint⟩ :=
    Target5314TaylorEndpoint.exists_concrete_taylor_endpoint selected hbranchSub
      Q R hRmem hRpos x₀ hdegree hresultant H hHpos hHdeg hHheight hHdvd
      hbranchHroot hbranchRroot
  exact Target5314Alignment.selectedPolynomialAlignment_of_concrete_taylor_endpoint
    selected hbranchSub hbranchCard x₀ R H hRpos hRdeg hdegree hresultant
      hPcoeff hHirr hHpos hHdeg hHheight hHdvd hbranchHroot hbranchRroot
      data hendpoint

end

end ProximityPrize.SubmissionLower.Target5314FullAlignment
