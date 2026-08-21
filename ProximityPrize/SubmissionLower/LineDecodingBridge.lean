/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# A minimal affine-alignment bridge to MCA error

This file isolates the final, purely finite part of affine-line decoding.  The hypothesis
`HasLargeAffineCollisionAlignment` is the exact output needed from an algebraic extraction
argument: if one fixed stack has more than `a` bad challenges, extraction supplies at least
`n + 1` challenges aligned with two codewords, and at every supplied challenge there is a
coordinate where the two affine combinations collide without both rows agreeing.

Two distinct affine collisions with the same coordinate force both rows to agree at that
coordinate.  Consequently the chosen collision coordinates are injective, contradicting the
existence of `n + 1` of them.  Averaging the resulting fixed-stack cardinality bound gives the
MCA error bound `a / |F|`.

Unlike the full line-decoding development, this bridge has no Hensel or rational-function
dependencies and imports only the challenge's trusted lower target.
-/

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [AddCommGroup A] [Module F A]

/-- The finite output contract required from affine-line extraction.

Whenever a fixed two-row stack has more than `a` MCA-bad field challenges, extraction must
produce two codewords and at least `|ι| + 1` challenges.  Each produced challenge has a
coordinate where the affine combinations agree, but at least one of the two rows disagrees.

The produced challenges need not be a subset of the original bad set.  This is deliberate:
curated-codeword versions of the line-decoding argument can produce additional close challenges
outside that set, and the final collision argument only needs their cardinality. -/
def HasLargeAffineCollisionAlignment
    (code : ModuleCode ι F A) (δ : ℝ) (a : ℕ) : Prop :=
  ∀ rows : Fin 2 → ι → A, ∀ bad : Finset F,
    (∀ gamma ∈ bad,
      IsMCA (AffineLineGenerator F) code gamma rows δ) →
    a < bad.card →
    ∃ code₀ code₁ : code, ∃ aligned : Finset F,
      Fintype.card ι + 1 ≤ aligned.card ∧
      ∀ gamma ∈ aligned, ∃ coordinate : ι,
        rows 0 coordinate + gamma • rows 1 coordinate =
            code₀.1 coordinate + gamma • code₁.1 coordinate ∧
          (rows 0 coordinate ≠ code₀.1 coordinate ∨
            rows 1 coordinate ≠ code₁.1 coordinate)

/-- Distinct affine collisions cannot use the same mismatching coordinate. -/
private theorem affineCollisionPick_injective
    (challenges : Finset F) (row₀ row₁ word₀ word₁ : ι → A)
    (pick : {gamma : F // gamma ∈ challenges} → ι)
    (hcollision : ∀ gamma,
      row₀ (pick gamma) + gamma.1 • row₁ (pick gamma) =
        word₀ (pick gamma) + gamma.1 • word₁ (pick gamma))
    (hmismatch : ∀ gamma,
      row₀ (pick gamma) ≠ word₀ (pick gamma) ∨
        row₁ (pick gamma) ≠ word₁ (pick gamma)) :
    Function.Injective pick := by
  intro gamma beta hpick
  apply Subtype.ext
  by_cases hvalue : gamma.1 = beta.1
  · exact hvalue
  · exfalso
    have hgamma := hcollision gamma
    have hbeta := hcollision beta
    rw [← hpick] at hbeta
    let difference₀ : A := row₀ (pick gamma) - word₀ (pick gamma)
    let difference₁ : A := row₁ (pick gamma) - word₁ (pick gamma)
    have hgamma' : difference₀ + gamma.1 • difference₁ = 0 := by
      calc
        difference₀ + gamma.1 • difference₁ =
            (row₀ (pick gamma) + gamma.1 • row₁ (pick gamma)) -
              (word₀ (pick gamma) + gamma.1 • word₁ (pick gamma)) := by
                dsimp only [difference₀, difference₁]
                skip <;> module
        _ = 0 := sub_eq_zero.mpr hgamma
    have hbeta' : difference₀ + beta.1 • difference₁ = 0 := by
      calc
        difference₀ + beta.1 • difference₁ =
            (row₀ (pick gamma) + beta.1 • row₁ (pick gamma)) -
              (word₀ (pick gamma) + beta.1 • word₁ (pick gamma)) := by
                dsimp only [difference₀, difference₁]
                skip <;> module
        _ = 0 := sub_eq_zero.mpr hbeta
    have hscalar : (gamma.1 - beta.1) • difference₁ = 0 := by
      calc
        (gamma.1 - beta.1) • difference₁ =
            (difference₀ + gamma.1 • difference₁) -
              (difference₀ + beta.1 • difference₁) := by skip <;> module
        _ = 0 := by rw [hgamma', hbeta']; simp only [sub_self]
    have hdifference₁ : difference₁ = 0 :=
      (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hvalue)
    have hdifference₀ : difference₀ = 0 := by
      rw [hdifference₁, smul_zero, add_zero] at hgamma'
      exact hgamma'
    have hrow₀ : row₀ (pick gamma) = word₀ (pick gamma) :=
      sub_eq_zero.mp (by simpa only [difference₀] using hdifference₀)
    have hrow₁ : row₁ (pick gamma) = word₁ (pick gamma) :=
      sub_eq_zero.mp (by simpa only [difference₁] using hdifference₁)
    exact (hmismatch gamma).elim (fun h => h hrow₀) (fun h => h hrow₁)

/-- A family of mismatching affine collisions has at most one challenge per coordinate. -/
private theorem affineCollision_card_le
    (challenges : Finset F) (row₀ row₁ word₀ word₁ : ι → A)
    (pick : {gamma : F // gamma ∈ challenges} → ι)
    (hcollision : ∀ gamma,
      row₀ (pick gamma) + gamma.1 • row₁ (pick gamma) =
        word₀ (pick gamma) + gamma.1 • word₁ (pick gamma))
    (hmismatch : ∀ gamma,
      row₀ (pick gamma) ≠ word₀ (pick gamma) ∨
        row₁ (pick gamma) ≠ word₁ (pick gamma)) :
    challenges.card ≤ Fintype.card ι := by
  have hcard := Fintype.card_le_of_injective pick
    (affineCollisionPick_injective challenges row₀ row₁ word₀ word₁
      pick hcollision hmismatch)
  simpa using hcard

open Classical in
/-- The extraction contract rules out more than `a` bad challenges for every fixed stack. -/
theorem HasLargeAffineCollisionAlignment.fixedStack_bad_card_le
    (code : ModuleCode ι F A) (δ : ℝ) (a : ℕ)
    (halign : HasLargeAffineCollisionAlignment code δ a)
    (rows : Fin 2 → ι → A) :
    (Finset.univ.filter fun gamma : F =>
      IsMCA (AffineLineGenerator F) code gamma rows δ).card ≤ a := by
  classical
  let bad := Finset.univ.filter fun gamma : F =>
    IsMCA (AffineLineGenerator F) code gamma rows δ
  change bad.card ≤ a
  by_contra hbound
  have habad : a < bad.card := Nat.lt_of_not_ge hbound
  have hbad : ∀ gamma ∈ bad,
      IsMCA (AffineLineGenerator F) code gamma rows δ := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  obtain ⟨code₀, code₁, aligned, halignedCard, haligned⟩ :=
    halign rows bad hbad habad
  have hexists : ∀ gamma : {gamma : F // gamma ∈ aligned}, ∃ coordinate : ι,
      rows 0 coordinate + gamma.1 • rows 1 coordinate =
          code₀.1 coordinate + gamma.1 • code₁.1 coordinate ∧
        (rows 0 coordinate ≠ code₀.1 coordinate ∨
          rows 1 coordinate ≠ code₁.1 coordinate) := by
    intro gamma
    exact haligned gamma.1 gamma.2
  choose pick hcollision hmismatch using hexists
  have hcard : aligned.card ≤ Fintype.card ι :=
    affineCollision_card_le aligned (rows 0) (rows 1) code₀.1 code₁.1
      pick hcollision hmismatch
  omega

/-- Averaging the fixed-stack cardinality bound gives the desired affine-line MCA error. -/
theorem HasLargeAffineCollisionAlignment.mcaError_le
    (code : ModuleCode ι F A) (δ : ℝ) (a : ℕ)
    (halign : HasLargeAffineCollisionAlignment code δ a) :
    mcaError (AffineLineGenerator F) code δ ≤
      (a : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  unfold mcaError
  refine iSup_le fun rows => ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast halign.fixedStack_bad_card_le code δ a rows

end

end CodingTheory
