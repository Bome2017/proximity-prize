import ProximityPrize.SubmissionLower.MCASelection5314
import ProximityPrize.SubmissionLower.LineDecodingBridge

namespace ProximityPrize.SubmissionLower

open Code CoreDefinitions ProximityGap ToyProblem Polynomial
open ProximityPrize.Benchmark

set_option maxRecDepth 100000

/-- Algebraic extraction contract isolated from the finite MCA collision argument. -/
def HasLargeSelectedPolynomialAlignment : Prop :=
  ∀ rows : Fin 2 → IRSProfile.Index → IRSProfile.Field,
    ∀ bad : Finset IRSProfile.Field,
    ∀ hbad : ∀ gamma ∈ bad,
      IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
        (targetRadius5314 : ℝ),
    ∀ selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1,
    2 ^ 57 < bad.card →
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      p₀.degree < IRSProfile.baseDimension ∧
      p₁.degree < IRSProfile.baseDimension ∧
      ∃ aligned : Finset IRSProfile.Field,
        ∃ alignedSub : aligned ⊆ bad,
        Fintype.card IRSProfile.Index + 1 ≤ aligned.card ∧
        ∀ gamma, ∀ hgamma : gamma ∈ aligned,
          (selected ⟨gamma, alignedSub hgamma⟩).polynomial =
            p₀ + Polynomial.C gamma * p₁

lemma evalPolynomial_mem_baseCode
    {p : Polynomial IRSProfile.Field}
    (hp : p.degree < IRSProfile.baseDimension) :
    ReedSolomon.evalOnPoints IRSProfile.domain p ∈ IRSProfile.baseCode := by
  exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt hp

lemma exists_collision_of_selected_polynomial_alignment
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {gamma : IRSProfile.Field}
    (hgamma : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ))
    (w : TargetBadSeedWitness rows gamma)
    (p₀ p₁ : Polynomial IRSProfile.Field)
    (hp₀ : p₀.degree < IRSProfile.baseDimension)
    (hp₁ : p₁.degree < IRSProfile.baseDimension)
    (halign : w.polynomial = p₀ + Polynomial.C gamma * p₁) :
    ∃ i : IRSProfile.Index,
      rows 0 i + gamma • rows 1 i =
          (ReedSolomon.evalOnPoints IRSProfile.domain p₀) i +
            gamma • (ReedSolomon.evalOnPoints IRSProfile.domain p₁) i ∧
        (rows 0 i ≠ (ReedSolomon.evalOnPoints IRSProfile.domain p₀) i ∨
          rows 1 i ≠ (ReedSolomon.evalOnPoints IRSProfile.domain p₁) i) := by
  classical
  have hmismatch : ∃ i ∈ w.support,
      rows 0 i ≠ (ReedSolomon.evalOnPoints IRSProfile.domain p₀) i ∨
        rows 1 i ≠ (ReedSolomon.evalOnPoints IRSProfile.domain p₁) i := by
    by_contra h
    push_neg at h
    obtain ⟨j, hj⟩ := w.nonprojection
    apply hj
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    fin_cases j
    · refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₀,
        evalPolynomial_mem_baseCode hp₀, ?_⟩
      funext i
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      exact h i.1 i.2 |>.1
    · refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₁,
        evalPolynomial_mem_baseCode hp₁, ?_⟩
      funext i
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      exact h i.1 i.2 |>.2
  obtain ⟨i, hi, himismatch⟩ := hmismatch
  refine ⟨i, ?_, himismatch⟩
  have hagree := w.agrees i hi
  rw [halign] at hagree
  simpa [AffineLineGenerator, Fin.sum_univ_two, ReedSolomon.evalOnPoints] using hagree.symm

theorem largeAffineCollisionAlignment_of_selectedPolynomialAlignment
    (hextract : HasLargeSelectedPolynomialAlignment) :
    CodingTheory.HasLargeAffineCollisionAlignment IRSProfile.baseCode
      (targetRadius5314 : ℝ) (2 ^ 57) := by
  intro rows bad hbad hcard
  let selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1 := fun gamma =>
    Classical.choice (exists_targetBadSeedWitness rows gamma.1 (hbad gamma.1 gamma.2))
  obtain ⟨p₀, p₁, hp₀, hp₁, aligned, halignedSub, halignedCard, haligned⟩ :=
    hextract rows bad hbad selected hcard
  let code₀ : IRSProfile.baseCode :=
    ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₀, evalPolynomial_mem_baseCode hp₀⟩
  let code₁ : IRSProfile.baseCode :=
    ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₁, evalPolynomial_mem_baseCode hp₁⟩
  refine ⟨code₀, code₁, aligned, halignedCard, ?_⟩
  intro gamma hgammaAligned
  have hgammaBad := halignedSub hgammaAligned
  let gammaSub : {gamma : IRSProfile.Field // gamma ∈ bad} := ⟨gamma, hgammaBad⟩
  have hseed : IsMCA (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode gamma rows
      (targetRadius5314 : ℝ) := hbad gamma hgammaBad
  obtain ⟨i, hcollision, hmismatch⟩ :=
    exists_collision_of_selected_polynomial_alignment hseed (selected gammaSub) p₀ p₁ hp₀ hp₁
      (haligned gamma hgammaAligned)
  exact ⟨i, by simpa [code₀, code₁] using hcollision,
    by simpa [code₀, code₁] using hmismatch⟩

end ProximityPrize.SubmissionLower
