import ProximityPrize.SubmissionLower.Cap72BadRoots5314
import ProximityPrize.SubmissionLower.Cap72SpecializedFactorAudit
import ProximityPrize.SubmissionLower.FiniteTaylorBetaInputs
import ProximityPrize.SubmissionLower.FiniteTaylorCapFactorHeight
import ProximityPrize.SubmissionLower.FiniteTaylorFactorQBridge

/-!
# Concrete Cap72 Taylor endpoint

This module constructs the four endpoint facts consumed by the final alignment
wrapper: outer degree, evaluated height, strict pre-remainder quotient degree,
and the retained-seed polynomial identity.
-/

namespace ProximityPrize.SubmissionLower.Target5314TaylorEndpoint

open scoped BigOperators
open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open Cap72BadRoots5314 Cap72FactorAudit Cap72SpecializedFactorAudit
open FiniteTaylorCore FiniteTaylorExtraction
open FiniteTaylorCap72Height FiniteTaylorCapFactorHeight
open FiniteTaylorBetaInputs Target5314Extraction

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option linter.constructorNameAsVariable false

private theorem commonDenominatorTaylorTruncation_natDegree_le
    {F : Type*} [Field F]
    (h k : Nat) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) :
    (commonDenominatorTaylorTruncation h k q seq).natDegree ≤ k := by
  classical
  unfold commonDenominatorTaylorTruncation
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

/-- Existentially packaged Taylor data.  Storing the concrete expressions as
equations avoids asking the kernel to normalize the entire construction when
checking each endpoint field. -/
structure ConcreteTaylorEndpointData
    (x₀ : IRSProfile.Field)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (H : Polynomial (Polynomial IRSProfile.Field)) where
  W : Polynomial IRSProfile.Field
  Hbar : Polynomial (Polynomial IRSProfile.Field)
  J : Polynomial (Polynomial IRSProfile.Field)
  q : Polynomial IRSProfile.Field
  G : Polynomial (Polynomial (Polynomial IRSProfile.Field))
  simple : Polynomial IRSProfile.Field
  W_eq : W = H.leadingCoeff
  Hbar_eq : Hbar = integralMonicize H
  J_eq : J = derivativeAtX x₀ (integralScale (Polynomial.C W) R)
  q_eq : q = (multiplicationMatrix H.natDegree Hbar J).det
  simple_eq : simple = FiniteTaylorFactorQBridge.simpleRootResultant
    (SequentialFactorSelection.specializeX x₀ R)

/-- All concrete facts required by
`selectedPolynomialAlignment_of_concrete_taylor_endpoint`. -/
theorem exists_concrete_taylor_endpoint
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad branch : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hbranchSub : branch ⊆ bad)
    (Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1))
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hRmem : R ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial)
    (hRpos : 0 < R.natDegree)
    (x₀ : IRSProfile.Field)
    (hdegree : (SequentialFactorSelection.specializeX x₀ R).natDegree =
      R.natDegree)
    (hresultant : (SequentialFactorSelection.derivativeResultant R).eval
      (Polynomial.C x₀) ≠ 0)
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hHpos : 0 < H.natDegree) (hHdeg : H.natDegree ≤ 11)
    (hHheight : ∀ i, (H.coeff i).natDegree ≤ 72)
    (hHdvd : H ∣ SequentialFactorSelection.specializeX x₀ R)
    (hbranchHroot : ∀ gamma ∈ branch,
      (FiniteTaylorExtraction.specializeZ gamma H).eval
        ((selectedPolynomial selected gamma).eval x₀) = 0)
    (hbranchRroot : ∀ gamma ∈ branch,
      Polynomial.eval₂ (RingHom.id (Polynomial IRSProfile.Field))
        (selectedPolynomial selected gamma)
        (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom gamma))) = 0) :
    ∃ data : ConcreteTaylorEndpointData x₀ R H,
      ConcreteTaylorEndpointContract (branch := branch) rows x₀
        (selectedPolynomial selected) data.W data.Hbar data.simple data.q
          data.G (data.q ^ oddDenomExponent 131071 * data.W) := by
  classical
  let P := SequentialFactorSelection.specializeX x₀ R
  set W := H.leadingCoeff with hWdef
  let Rbar := integralScale (Polynomial.C W) R
  set Hbar := integralMonicize H with hHbardef
  set J := derivativeAtX x₀ (integralScale (Polynomial.C W) R) with hJdef
  set q := (multiplicationMatrix H.natDegree Hbar J).det with hqdef
  set seq := concreteTaylorNumerators x₀
    (integralScale (Polynomial.C W) R) H.natDegree Hbar J
      (quotientVariableVector H.natDegree Hbar) with hseqdef
  let S := commonDenominatorTaylorTruncation H.natDegree 131071 q seq
  set G := unshiftTaylor x₀
    (commonDenominatorTaylorTruncation H.natDegree 131071 q seq) with hGdef
  set simple := FiniteTaylorFactorQBridge.simpleRootResultant
    (SequentialFactorSelection.specializeX x₀ R) with hsimpledef
  set scale := q ^ oddDenomExponent 131071 * W with hscaledef
  have hRdvd : R ∣ Q.polynomial :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRmem
  have hR0 : R ≠ 0 := by
    intro hzero
    apply UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q.polynomial
    simpa [hzero] using hRmem
  have hRdeg : R.natDegree ≤ 11 := factor_natDegree_le_eleven Q hRdvd
  have hWdeg : W.natDegree ≤ 72 := by
    exact hHheight H.natDegree
  have hPcoeff : ∀ i, (P.coeff i).natDegree ≤ 72 := by
    intro i
    have htotal := specializeX_totalDegree_le_seventyTwo Q hRdvd hR0 x₀
    rcases Polynomial.Bivariate.coeff_totalDegree_le' P i with h | h
    · exact (Nat.le_add_right _ _).trans (h.trans (by simpa [P] using htotal))
    · simp [h]
  have hHbarMonic : Hbar.Monic := by
    simpa [Hbar] using integralMonicize_monic H
  have hHbarDeg : Hbar.natDegree = H.natDegree := by
    simp [Hbar, integralMonicize_natDegree]
  have hHbarHeight : polyHeight Hbar ≤ 792 := by
    simpa [Hbar] using integralMonicize_polyHeight_le_792 H hHdeg hHheight
  have hJdeg : J.natDegree ≤ 10 := by
    simpa [J, Rbar, W] using
      (FiniteTaylorFactorQBridge.concrete_derivativeAtX_natDegree_le_ten
        x₀ H.leadingCoeff R hRdeg hdegree)
  have hJheight : polyHeight J ≤ 864 := by
    simpa [J, Rbar, W] using
      (FiniteTaylorFactorQBridge.concrete_derivativeAtX_polyHeight_le_864
        x₀ H.leadingCoeff R hRdeg hdegree hPcoeff hWdeg)
  have hqdeg : q.natDegree ≤ 400000 := by
    rw [hqdef]
    exact cap72_multiplicationMatrix_det_natDegree_le_400000
      H.natDegree Hbar J hHdeg hHbarHeight hJdeg hJheight
  have hRbarDeg : Rbar.natDegree ≤ 11 := by
    have heq : Rbar = R.scaleRoots (Polynomial.C W) := by
      change FiniteTaylorIntegralScale.integralScaleAt R.natDegree
        (Polynomial.C W) R = R.scaleRoots (Polynomial.C W)
      exact FiniteTaylorIntegralScale.integralScaleAt_eq_scaleRoots
        R.natDegree (Polynomial.C W) R rfl
    rw [heq, Polynomial.natDegree_scaleRoots]
    exact hRdeg
  have hRcoeff : ∀ j, polyHeight (R.coeff j) ≤ 72 := by
    intro j
    exact factor_coeff_polyHeight_le_seventyTwo Q hRdvd hR0 j
  have hRbarShiftHeight : ∀ j,
      polyHeight ((shiftX x₀ Rbar).coeff j) ≤ 864 := by
    intro j
    simpa [Rbar, W] using
      (FiniteTaylorFactorQBridge.concrete_shiftX_integralScale_coeff_polyHeight_le_864
        x₀ H.leadingCoeff R hRdeg hRcoeff hWdeg j)
  have ha0 : vectorHeight (quotientVariableVector H.natDegree Hbar) ≤ 1000 :=
    quotientVariableVector_height_le_1000 H.natDegree Hbar hHpos
      hHbarDeg hHbarMonic hHbarHeight
  have hseq : ∀ i ≤ 131071, vectorHeight (seq i) ≤ 10000000000000 := by
    intro i hi
    rw [congrFun hseqdef i]
    change vectorHeight (concreteTaylorNumerators x₀ Rbar H.natDegree
      Hbar J (quotientVariableVector H.natDegree Hbar) i) ≤ 10000000000000
    exact cap72_concreteTaylorNumerators_height_le_10pow13
      x₀ Rbar H.natDegree Hbar J
      (quotientVariableVector H.natDegree Hbar)
      hHpos hHdeg hHbarMonic hHbarDeg hHbarHeight hJdeg hJheight
      hRbarDeg hRbarShiftHeight ha0 i hi
  have hGdegree : G.natDegree ≤ 131071 := by
    have hSdegree := commonDenominatorTaylorTruncation_natDegree_le
      (F := IRSProfile.Field) H.natDegree 131071 q seq
    exact (natDegree_unshiftTaylor_le x₀ S).trans (by
      simpa [S] using hSdegree)
  have hGeval : ∀ s, polyHeight
      (G.eval (Polynomial.C (Polynomial.C s))) ≤ 10104857200000 := by
    intro s
    exact polyHeight_eval_unshifted_commonDenominatorTaylorTruncation_le
      x₀ H.natDegree 131071 q seq (by omega) hqdeg hseq s
  have hHbarDegree : Hbar.degree = (H.natDegree : WithBot Nat) := by
    rw [Hbar.degree_eq_natDegree hHbarMonic.ne_zero, hHbarDeg]
  have hpredegree : ∀ i,
      (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
        Polynomial.C
          (scale * (Polynomial.C (rows 0 i) +
            Polynomial.X * Polynomial.C (rows 1 i)))).degree < Hbar.degree := by
    intro i
    rw [hHbarDegree]
    exact unshifted_beta_predegree_rows_lt rows x₀ H.natDegree 131071
      hHpos q seq scale i
  have hscaleDegree : scale.natDegree + 1 ≤ 10104857200000 := by
    simpa [scale] using cap72_scale_natDegree_add_one_le q W hqdeg hWdeg
  have hbetaHeight : BetaHeightContract rows Hbar G scale := {
    bound := canonical_beta_height_le rows Hbar hHbarMonic G scale hGeval
      hscaleDegree hpredegree }
  let data : ConcreteTaylorEndpointData x₀ R H := {
    W := W
    Hbar := Hbar
    J := J
    q := q
    G := G
    simple := simple
    W_eq := hWdef
    Hbar_eq := hHbardef
    J_eq := hJdef
    q_eq := hqdef
    simple_eq := hsimpledef }
  refine ⟨data, ?_⟩
  dsimp only [data]
  rw [← hscaledef]
  refine {
    Gdegree := by exact hGdegree
    Geval := fun s => hGeval s
    predegree := fun i => hpredegree i
    betaHeight := { bound := fun i j => hbetaHeight.bound i j }
    Gseed := ?_ }
  intro gamma hgamma
  have hgood := goodSeeds_eval_ne_zero branch W simple q hgamma
  have hgammaBranch : gamma ∈ branch :=
    goodSeeds_subset branch W simple q hgamma
  have hgammaBad : gamma ∈ bad := hbranchSub hgammaBranch
  let p := selectedPolynomial selected gamma
  have hpdeg : p.natDegree ≤ 131071 :=
    selectedPolynomial_natDegree_le selected hgammaBad
  have hHroot : (FiniteTaylorExtraction.specializeZ gamma H).eval
      (p.eval x₀) = 0 := hbranchHroot gamma hgammaBranch
  have hRroot : Polynomial.eval₂
      (RingHom.id (Polynomial IRSProfile.Field)) p
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom gamma))) = 0 :=
    hbranchRroot gamma hgammaBranch
  have hJne : (FiniteTaylorExtraction.specializeZ gamma J).eval
      (W.eval gamma * p.eval x₀) ≠ 0 := by
    rw [hJdef, hWdef]
    exact FiniteTaylorFactorQBridge.concrete_integralizedDerivative_eval_ne_zero
      x₀ gamma (p.eval x₀) R H hRpos hdegree hHdvd hHroot hgood.1
        hgood.2.1
  have hJexplicit := hJne
  rw [hJdef, hWdef] at hJexplicit
  have hmap := map_unshifted_integralized_commonTaylorTruncation
    x₀ gamma R H H.natDegree 131071 hHpos rfl p hpdeg hHroot hRroot
      hgood.2.2 hJexplicit
  dsimp only at hmap
  rw [← hWdef] at hmap
  rw [← hHbardef] at hmap
  rw [← hJdef] at hmap
  rw [← hqdef] at hmap
  rw [← hseqdef] at hmap
  rw [hGdef, hscaledef]
  simpa only [p, Polynomial.eval_mul, Polynomial.eval_pow] using hmap

end

end ProximityPrize.SubmissionLower.Target5314TaylorEndpoint
