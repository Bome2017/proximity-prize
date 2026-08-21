import ProximityPrize.SubmissionLower.Cap72SecondBranch5314
import ProximityPrize.SubmissionLower.Target5314Extraction
import ProximityPrize.SubmissionLower.Target5314TaylorEndpoint

/-!
# Final 53.14 alignment extraction

This module instantiates the branch-independent Taylor/resultant assembly with
the concrete second Cap72 factor selected by `Cap72SecondBranch5314`.
-/

namespace ProximityPrize.SubmissionLower.Target5314Alignment

open scoped BigOperators
open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open Cap72BadRoots5314 Cap72SecondBranch5314 Cap72FactorAudit
open Cap72SpecializedFactorAudit
open FactorThreshold5314
open FiniteTaylorCore FiniteTaylorExtraction
open Target5314Extraction

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 300000
set_option linter.constructorNameAsVariable false

/-- Every specialization coefficient of the preserved Cap72 factor obeys the
same `Z`-degree cap as its swapped `(Z,Y)` total degree. -/
theorem specializedFactor_coeff_natDegree_le_seventyTwo
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1))
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hRdvd : R ∣ Q.polynomial) (hR0 : R ≠ 0)
    (x₀ : IRSProfile.Field) (i : Nat) :
    ((SequentialFactorSelection.specializeX x₀ R).coeff i).natDegree ≤ 72 := by
  have htotal := specializeX_totalDegree_le_seventyTwo Q hRdvd hR0 x₀
  rcases Polynomial.Bivariate.coeff_totalDegree_le'
      (SequentialFactorSelection.specializeX x₀ R) i with h | h
  · exact (Nat.le_add_right _ _).trans (h.trans htotal)
  · simp [h]

/-- The first Cap72 factor has coefficientwise `Z` height at most `72`; this
is the same swapped `(Z,Y)` grading used in the specialization audit. -/
theorem factor_coeff_polyHeight_le_seventyTwo
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1))
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hRdvd : R ∣ Q.polynomial) (hR0 : R ≠ 0) (j : Nat) :
    polyHeight (R.coeff j) ≤ 72 := by
  have htotal := factor_totalDegree_swapZX_le Q hRdvd hR0
  have hcoeff : ((swapZX R).coeff j).natDegree ≤ 72 := by
    by_cases hz : (swapZX R).coeff j = 0
    · simp [hz]
    · have hmem : j ∈ (swapZX R).support :=
        Polynomial.mem_support_iff.mpr hz
      have hc := Polynomial.Bivariate.coeff_totalDegree_le (swapZX R) hmem
      omega
  change ((R.map Polynomial.Bivariate.swap.toRingEquiv.toRingHom).coeff j).natDegree ≤ 72
    at hcoeff
  rw [Polynomial.coeff_map] at hcoeff
  change Polynomial.Bivariate.natDegreeY
    (Polynomial.Bivariate.swap (R.coeff j)) ≤ 72 at hcoeff
  change Polynomial.Bivariate.degreeX (R.coeff j) ≤ 72
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  exact hcoeff

/-- Scalar evaluation of the common truncation stays in the quotient basis
`1,T,...,T^(h-1)`.  This is the pre-remainder degree fact which makes the
final beta height estimate lossless. -/
theorem commonDenominatorTaylorTruncation_eval_degree_lt
    {F : Type*} [Field F]
    (h k : Nat) (hh : 0 < h) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) (s : F) :
    ((commonDenominatorTaylorTruncation h k q seq).eval
      (Polynomial.C (Polynomial.C s))).degree < h := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  have hhn : h ≤ n := by exact_mod_cast hn
  unfold commonDenominatorTaylorTruncation
  rw [Polynomial.eval_finset_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.eval_monomial, Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases hb0 : ab.2 = 0
  · have ha : ab.1 = n := by
      have habsum : ab.1 + ab.2 = n := Finset.mem_antidiagonal.mp hab
      omega
    rw [hb0, ha]
    rw [← map_pow, Polynomial.coeff_C_mul,
      coeff_vectorPolynomial_eq_zero_of_le h (seq i) n hhn]
    simp
  · have hz : ((Polynomial.C (Polynomial.C s) :
        Polynomial (Polynomial F)) ^ i.1).coeff ab.2 = 0 := by
      rw [← map_pow, Polynomial.coeff_C]
      exact if_neg hb0
    rw [hz, mul_zero]

/-- Recentering the Taylor variable and then specializing the outer variable
preserves the strict quotient-variable degree bound. -/
theorem unshiftTaylor_eval_degree_lt
    {F : Type*} [Field F]
    (x₀ s : F) (h k : Nat) (hh : 0 < h) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) :
    ((unshiftTaylor x₀ (commonDenominatorTaylorTruncation h k q seq)).eval
      (Polynomial.C (Polynomial.C s))).degree < h := by
  unfold unshiftTaylor
  rw [Polynomial.eval_comp]
  convert commonDenominatorTaylorTruncation_eval_degree_lt
    h k hh q seq (s - x₀) using 1 <;> simp

/-- Concrete second-branch assembly with only the four Taylor endpoint facts
grouped as an explicit premise.  All exceptional-polynomial, monicization,
resultant-degree, and final rich-fiber obligations are discharged here. -/
theorem selectedPolynomialAlignment_of_concrete_taylor_endpoint
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad branch : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hbranchSub : branch ⊆ bad)
    (hbranchCard : FactorThreshold5314.branchThreshold < branch.card)
    (x₀ : IRSProfile.Field)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hRpos : 0 < R.natDegree) (hRdeg : R.natDegree ≤ 11)
    (hdegree : (SequentialFactorSelection.specializeX x₀ R).natDegree =
      R.natDegree)
    (hresultant : (SequentialFactorSelection.derivativeResultant R).eval
      (Polynomial.C x₀) ≠ 0)
    (hPcoeff : ∀ i,
      ((SequentialFactorSelection.specializeX x₀ R).coeff i).natDegree ≤ 72)
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHdeg : H.natDegree ≤ 11)
    (hHheight : ∀ i, (H.coeff i).natDegree ≤ 72)
    (hHdvd : H ∣ SequentialFactorSelection.specializeX x₀ R)
    (hbranchHroot : ∀ gamma ∈ branch,
      (specializeZ gamma H).eval
        ((selectedPolynomial selected gamma).eval x₀) = 0)
    (hbranchRroot : ∀ gamma ∈ branch,
      Polynomial.eval₂ (RingHom.id (Polynomial IRSProfile.Field))
        (selectedPolynomial selected gamma)
        (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom gamma))) = 0)
    (data : Target5314TaylorEndpoint.ConcreteTaylorEndpointData x₀ R H)
    (hendpoint : ConcreteTaylorEndpointContract (branch := branch) rows x₀
      (selectedPolynomial selected) data.W data.Hbar data.simple data.q data.G
        (data.q ^ oddDenomExponent 131071 * data.W)) :
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      p₀.degree < IRSProfile.baseDimension ∧
      p₁.degree < IRSProfile.baseDimension ∧
      ∃ aligned : Finset IRSProfile.Field,
        ∃ alignedSub : aligned ⊆ bad,
          Fintype.card IRSProfile.Index + 1 ≤ aligned.card ∧
          ∀ gamma, ∀ hgamma : gamma ∈ aligned,
            (selected ⟨gamma, alignedSub hgamma⟩).polynomial =
              p₀ + Polynomial.C gamma * p₁ := by
  classical
  set P := SequentialFactorSelection.specializeX x₀ R with hPdef
  let W := data.W
  let Hbar := data.Hbar
  let J := data.J
  let q := data.q
  let G := data.G
  let simple := data.simple
  have hWdef : W = H.leadingCoeff := data.W_eq
  have hHbardef : Hbar = integralMonicize H := data.Hbar_eq
  have hJdef : J = derivativeAtX x₀ (integralScale (Polynomial.C W) R) :=
    data.J_eq
  have hqdef : q = (multiplicationMatrix H.natDegree Hbar J).det := data.q_eq
  have hsimpledef : simple = FiniteTaylorFactorQBridge.simpleRootResultant P := by
    simpa only [P] using data.simple_eq
  let yAt : IRSProfile.Field → IRSProfile.Field := fun gamma =>
    W.eval gamma * (selectedPolynomial selected gamma).eval x₀
  let support : IRSProfile.Field → Finset IRSProfile.Index := fun gamma =>
    if hgamma : gamma ∈ bad then (selected ⟨gamma, hgamma⟩).support else ∅
  have hGdegree := hendpoint.Gdegree
  have hGeval := hendpoint.Geval
  have hpredegree := hendpoint.predegree
  have hbetaHeight := hendpoint.betaHeight
  have hGseed := hendpoint.Gseed
  have hW : W ≠ 0 := by
    rw [hWdef]
    exact Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hHpos)
  have hWdeg : W.natDegree ≤ 72 := by
    rw [hWdef]
    exact hHheight H.natDegree
  have hPpos : 0 < P.natDegree := by rw [hdegree]; exact hRpos
  have hPdeg : P.natDegree ≤ 11 := by rw [hdegree]; exact hRdeg
  have hsimple : simple ≠ 0 := by
    rw [hsimpledef]
    exact simpleRootResultant_ne_zero P hPpos hPdeg
      (by simpa [hPdef] using
        (SequentialFactorSelection.fractionMap_specializeX_separable
          R x₀ hRpos hresultant))
  have hsimpleDeg : simple.natDegree ≤ 1512 := by
    rw [hsimpledef]
    simpa [FiniteTaylorFactorQBridge.simpleRootResultant] using
      (simpleRootResultant_natDegree_le_1512 P hPdeg hPcoeff)
  have hq : q ≠ 0 := by
    rw [hqdef, hHbardef, hJdef, hWdef]
    exact FiniteTaylorFactorQBridge.concrete_taylorDet_ne_zero
      x₀ R H hRpos hRdeg hdegree hresultant hHpos hHdvd
  have hHbarMonic : Hbar.Monic := by
    rw [hHbardef]
    exact integralMonicize_monic H
  have hHbarPos : 0 < Hbar.natDegree := by
    rw [hHbardef, integralMonicize_natDegree]
    exact hHpos
  have hHbarDeg : Hbar.natDegree ≤ 11 := by
    rw [hHbardef, integralMonicize_natDegree]
    exact hHdeg
  have hHbarHeight : polyHeight Hbar ≤ 792 := by
    rw [hHbardef]
    exact integralMonicize_polyHeight_le_792 H hHdeg hHheight
  have hHbarIrr : Irreducible
      (Hbar.map (algebraMap (Polynomial IRSProfile.Field)
        (FractionRing (Polynomial IRSProfile.Field)))) := by
    rw [hHbardef]
    exact integralMonicize_fraction_irreducible H hHirr hHpos
  have hJdegree : J.natDegree ≤ 10 := by
    rw [hJdef, hWdef]
    exact FiniteTaylorFactorQBridge.concrete_derivativeAtX_natDegree_le_ten
      x₀ H.leadingCoeff R hRdeg hdegree
  have hJheight : polyHeight J ≤ 864 := by
    rw [hJdef, hWdef]
    exact FiniteTaylorFactorQBridge.concrete_derivativeAtX_polyHeight_le_864
      x₀ H.leadingCoeff R hRdeg hdegree hPcoeff (hHheight H.natDegree)
  have hqdeg : q.natDegree ≤ 400000 := by
    rw [hqdef]
    exact FiniteTaylorExtraction.cap72_multiplicationMatrix_det_natDegree_le_400000
      H.natDegree Hbar J hHdeg hHbarHeight hJdegree hJheight
  apply selectedPolynomialAlignment_of_filtered_taylor_data selected hbranchSub
    W simple q hbranchCard hW hsimple hq hWdeg hsimpleDeg hqdeg Hbar
    hHbarMonic hHbarPos hHbarDeg hHbarHeight hHbarIrr G hGdegree yAt
    (support := support)
  · intro gamma hgamma
    dsimp only [yAt]
    rw [hHbardef, hWdef]
    exact integralMonicize_specialized_root H hHpos gamma _
      (hbranchHroot gamma (goodSeeds_subset branch W simple q hgamma))
  · intro gamma hgamma
    have hbad := hbranchSub (goodSeeds_subset branch W simple q hgamma)
    have hsel : selectedPolynomial selected gamma =
        (selected ⟨gamma, hbad⟩).polynomial := by
      rw [selectedPolynomial, dif_pos hbad]
    rw [← hsel]
    simpa only [W, G, q, yAt, FiniteTaylorExtraction.evalZT] using
      hGseed gamma hgamma
  · intro gamma hgamma
    have hbad := hbranchSub (goodSeeds_subset branch W simple q hgamma)
    change (if h : gamma ∈ bad then (selected ⟨gamma, h⟩).support else ∅) = _
    rw [dif_pos hbad]
  · simpa only [W, G, q] using hbetaHeight

end

end ProximityPrize.SubmissionLower.Target5314Alignment
