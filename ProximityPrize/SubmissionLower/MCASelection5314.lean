import ProximityPrize.SubmissionLower.Target5314

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem Polynomial
open ProximityPrize.Benchmark

set_option maxRecDepth 100000

/-- Concrete Reed--Solomon data selected from one bad affine-line challenge. -/
structure TargetBadSeedWitness
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field) where
  support : Finset IRSProfile.Index
  support_card : support.card = 196592
  polynomial : Polynomial IRSProfile.Field
  polynomial_degree : polynomial.degree < IRSProfile.baseDimension
  agrees : ∀ i ∈ support,
    polynomial.eval (IRSProfile.domain i) =
      ∑ j, AffineLineGenerator IRSProfile.Field gamma j • rows j i
  nonprojection : ∃ j : Fin 2,
    LinearCode.projectedWord (rows j) support ∉
      LinearCode.projectedCodeSubmod IRSProfile.baseCode support

lemma exists_targetBadSeedWitness
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ)) :
    Nonempty (TargetBadSeedWitness rows gamma) := by
  obtain ⟨support, hcard, hcomb, hnonproj⟩ :=
    exists_target5314_exact_support rows gamma hgamma
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨codeword, hcodeword, hagree⟩ := hcomb
  change codeword ∈ ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension at hcodeword
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcodeword
  obtain ⟨p, hpdegree, rfl⟩ := hcodeword
  refine ⟨⟨support, hcard, p, hpdegree, ?_, hnonproj⟩⟩
  intro i hi
  have h := congrFun hagree ⟨i, hi⟩
  simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using h.symm

noncomputable def targetBadSeedWitness
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (gamma : IRSProfile.Field)
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ)) :
    TargetBadSeedWitness rows gamma :=
  Classical.choice (exists_targetBadSeedWitness rows gamma hgamma)

lemma targetBadSeedWitness_agrees_affine
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {gamma : IRSProfile.Field}
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ))
    (i : IRSProfile.Index) (hi : i ∈ (targetBadSeedWitness rows gamma hgamma).support) :
    (targetBadSeedWitness rows gamma hgamma).polynomial.eval (IRSProfile.domain i) =
      rows 0 i + gamma * rows 1 i := by
  simpa [AffineLineGenerator, Fin.sum_univ_two] using
    (targetBadSeedWitness rows gamma hgamma).agrees i hi

end ProximityPrize.SubmissionLower
