import ProximityPrize.SubmissionLower.Cap72FirstFactor5314
import ProximityPrize.SubmissionLower.Cap72RootVanishing
import ProximityPrize.SubmissionLower.MCASelection5314

namespace ProximityPrize.SubmissionLower

open Polynomial Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark

namespace Cap72BadRoots5314

open Cap72 Cap72Root Cap72FactorSelection Cap72FirstFactor5314
  FactorThreshold5314

set_option maxRecDepth 1000000

/-- Extend a family indexed by a finite set to a total polynomial-valued function. -/
noncomputable def selectedPolynomial
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1) :
    IRSProfile.Field → Polynomial IRSProfile.Field := fun gamma =>
  if hgamma : gamma ∈ bad then (selected ⟨gamma, hgamma⟩).polynomial else 0

lemma selectedPolynomial_natDegree_le
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    {gamma : IRSProfile.Field} (hgamma : gamma ∈ bad) :
    (selectedPolynomial selected gamma).natDegree ≤ 131071 := by
  classical
  rw [selectedPolynomial, dif_pos hgamma]
  by_cases hp : (selected ⟨gamma, hgamma⟩).polynomial = 0
  · simp [hp]
  · have hlt : (selected ⟨gamma, hgamma⟩).polynomial.natDegree < 131072 := by
      apply (Polynomial.natDegree_lt_iff_degree_lt hp).2
      simpa [IRSProfile.baseDimension] using
        (selected ⟨gamma, hgamma⟩).polynomial_degree
    omega

lemma selectedPolynomial_agrees
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    {gamma : IRSProfile.Field} (hgamma : gamma ∈ bad)
    {i : IRSProfile.Index} (hi : i ∈ (selected ⟨gamma, hgamma⟩).support) :
    (selectedPolynomial selected gamma).eval (IRSProfile.domain i) =
      rows 0 i + gamma * rows 1 i := by
  classical
  rw [selectedPolynomial, dif_pos hgamma]
  simpa [AffineLineGenerator, Fin.sum_univ_two] using
    (selected ⟨gamma, hgamma⟩).agrees i hi

/-- Every selected close polynomial is an exact root of the capped interpolant
after its seed is specialized. -/
theorem interpolant_roots_selected
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1)) :
    ∀ gamma ∈ bad,
      Cap72FactorSelection.specializeAt gamma (selectedPolynomial selected gamma)
        Q.polynomial = 0 := by
  intro gamma hgamma
  have hroot := Cap72Root.composeAtSeed_eq_zero_of_many_agreements
    Q gamma (selectedPolynomial selected gamma)
    (selectedPolynomial_natDegree_le selected hgamma)
    (selected ⟨gamma, hgamma⟩).support
    (by rw [(selected ⟨gamma, hgamma⟩).support_card])
    IRSProfile.domain.injective
    (fun i hi => selectedPolynomial_agrees selected hgamma hi)
  simpa [Cap72FactorSelection.specializeAt, Cap72Root.composeAtSeed,
    Cap72Root.specializeZ] using hroot

/-- First fixed irreducible branch for an arbitrary bad-seed family larger
than `2^57`.  The branch is intentionally large enough for the second `/11`. -/
theorem exists_interpolant_and_large_first_factor
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hcard : 2 ^ 57 < bad.card) :
    ∃ Q : Cap72.Interpolant IRSProfile.domain (rows 0) (rows 1),
      ∃ R,
        R ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial ∧
        Irreducible R ∧
        0 < R.natDegree ∧
        11 * branchThreshold + 72 <
          (bad.filter fun gamma =>
            Cap72FactorSelection.specializeAt gamma
              (selectedPolynomial selected gamma) R = 0).card := by
  obtain ⟨Q⟩ := Cap72.exists_interpolant IRSProfile.domain (rows 0) (rows 1)
  refine ⟨Q, ?_⟩
  exact Cap72FirstFactor5314.exists_large_first_factor Q bad
    (selectedPolynomial selected) (interpolant_roots_selected selected Q) hcard

end Cap72BadRoots5314

end ProximityPrize.SubmissionLower
