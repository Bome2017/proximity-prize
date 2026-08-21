import ProximityPrize.SubmissionLower.Cap72BadRoots5314
import ProximityPrize.SubmissionLower.Cap72SpecializedFactorAudit
import ProximityPrize.SubmissionLower.FactorThreshold5314

namespace ProximityPrize.SubmissionLower.Cap72SecondBranch5314

open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open Cap72BadRoots5314 Cap72SpecializedFactorAudit FactorThreshold5314

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

noncomputable section

/-- Evaluating a first-branch root identity after `X := x₀` gives exactly the
root identity required by the second factor selection. -/
lemma evalZY_specializeX_eq_eval_specializeAt
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (gamma x₀ : IRSProfile.Field) (p : Polynomial IRSProfile.Field) :
    SequentialFactorSelection.evalZY gamma (p.eval x₀)
        (SequentialFactorSelection.specializeX x₀ R) =
      (Cap72FactorSelection.specializeAt gamma p R).eval x₀ := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      unfold SequentialFactorSelection.evalZY at hR hS ⊢
      simp only [map_add, Polynomial.eval_add] at hR hS ⊢
      rw [Polynomial.map_add, Polynomial.eval_add]
      exact congrArg₂ (fun u v => u + v) hR hS
  | monomial n a =>
      induction a using Polynomial.induction_on' with
      | add a b ha hb =>
          unfold SequentialFactorSelection.evalZY at ha hb ⊢
          simp only [map_add, Polynomial.eval_add] at ha hb ⊢
          rw [Polynomial.map_add, Polynomial.eval_add]
          exact congrArg₂ (fun u v => u + v) ha hb
      | monomial m b =>
          simp [SequentialFactorSelection.evalZY,
            SequentialFactorSelection.specializeX,
            Cap72FactorSelection.specializeAt, Function.comp_def,
            mul_pow]

/-- The complete two-factor Cap72 branch, retaining the corrected margin
`branchThreshold = 2^50 + 2^45` for the later exceptional-set removal. -/
theorem exists_second_branch
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hcard : 2 ^ 57 < bad.card) :
    ∃ Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1),
      ∃ R : Polynomial (Polynomial (Polynomial IRSProfile.Field)),
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial ∧
        Irreducible R ∧
        0 < R.natDegree ∧
        R.natDegree ≤ 11 ∧
        ∃ x₀ ∈ (Finset.univ : Finset IRSProfile.Field),
          (SequentialFactorSelection.specializeX x₀ R).natDegree = R.natDegree ∧
          (SequentialFactorSelection.derivativeResultant R).eval
            (Polynomial.C x₀) ≠ 0 ∧
          ∃ H : Polynomial (Polynomial IRSProfile.Field),
            H ∈ UniqueFactorizationMonoid.normalizedFactors
              (SequentialFactorSelection.specializeX x₀ R) ∧
            Irreducible H ∧
            0 < H.natDegree ∧
            H.natDegree ≤ 11 ∧
            (∀ i, (H.coeff i).natDegree ≤ 72) ∧
            H ∣ SequentialFactorSelection.specializeX x₀ R ∧
            (SequentialFactorSelection.fractionMap
              (SequentialFactorSelection.specializeX x₀ R)).Separable ∧
            (SequentialFactorSelection.fractionMap H).Separable ∧
            branchThreshold <
              ((bad.filter fun gamma =>
                Cap72FactorSelection.specializeAt gamma
                  (selectedPolynomial selected gamma) R = 0).filter fun gamma =>
                SequentialFactorSelection.evalZY gamma
                  ((selectedPolynomial selected gamma).eval x₀) H = 0).card := by
  classical
  obtain ⟨Q, R, hRmem, hRirr, hRpos, hfirst⟩ :=
    exists_interpolant_and_large_first_factor selected hcard
  let first := bad.filter fun gamma =>
    Cap72FactorSelection.specializeAt gamma
      (selectedPolynomial selected gamma) R = 0
  have hroot : ∀ x₀, ∀ gamma ∈ first,
      SequentialFactorSelection.evalZY gamma
        ((selectedPolynomial selected gamma).eval x₀)
        (SequentialFactorSelection.specializeX x₀ R) = 0 := by
    intro x₀ gamma hgamma
    have hs := (Finset.mem_filter.mp hgamma).2
    rw [evalZY_specializeX_eq_eval_specializeAt, hs]
    simp
  have hinj : Set.InjOn (fun gamma : IRSProfile.Field => gamma)
      (first : Set IRSProfile.Field) := by
    intro a _ b _ hab
    exact hab
  obtain ⟨x₀, hx₀, hPdegree, hresultant, H, hHmem, hHirr, hHpos, hHdeg, hHheight,
      hHdvd, hPsep, hHsep, hsecond⟩ :=
    exists_good_specialization_and_fixed_factor_cap72 Q R hRmem hRpos
      first id (fun x gamma => (selectedPolynomial selected gamma).eval x)
      hinj hroot (threshold := branchThreshold) (by simpa [first] using hfirst)
  have hRdvd : R ∣ Q.polynomial :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRmem
  have hRdeg : R.natDegree ≤ 11 :=
    Cap72FactorAudit.factor_natDegree_le_eleven Q hRdvd
  refine ⟨Q, R, hRmem, hRirr, hRpos, hRdeg, x₀, ?_⟩
  constructor
  · simp
  constructor
  · exact hPdegree
  constructor
  · exact hresultant
  refine ⟨H, ?_⟩
  constructor
  · exact hHmem
  constructor
  · exact hHirr
  constructor
  · exact hHpos
  constructor
  · exact hHdeg
  constructor
  · exact hHheight
  constructor
  · exact hHdvd
  constructor
  · exact hPsep
  constructor
  · exact hHsep
  simpa [first] using hsecond

end

end ProximityPrize.SubmissionLower.Cap72SecondBranch5314
