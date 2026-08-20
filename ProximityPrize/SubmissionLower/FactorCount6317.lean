/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.Divisibility6317

/-!
# Improved BCHKS factor-cell bookkeeping

The saving from `DY^3` to `DY^2` is an aggregate degree calculation, not a uniform
per-factor estimate.  This file keeps that calculation explicit so the final proof cannot
accidentally reintroduce the lost factor.
-/

namespace ProximityPrize.SubmissionLower

open scoped BigOperators

section FactorCounting

/-- A cover by factor cells converts per-cell cardinality bounds into a global bound. -/
theorem card_le_content_add_sum_cells
    {F A : Type} [Fintype F] [DecidableEq F] [Fintype A]
    (bad content : Finset F) (cell : A → Finset F)
    (hcover : bad ⊆ content ∪ Finset.univ.biUnion cell) :
    bad.card ≤ content.card + ∑ a : A, (cell a).card := by
  classical
  calc
    bad.card ≤ (content ∪ Finset.univ.biUnion cell).card :=
      Finset.card_le_card hcover
    _ ≤ content.card + (Finset.univ.biUnion cell).card := Finset.card_union_le _ _
    _ ≤ content.card + ∑ a : A, (cell a).card := by
      exact Nat.add_le_add_left (Finset.card_biUnion_le) _

/-- The abstract improved-degree summation.  `R` indexes irreducible `Y`-factors and
`H i` their specialized irreducible factors. -/
theorem improved_factor_degree_sum
    {R : Type} [Fintype R] (H : R → Type)
    [∀ i, Fintype (H i)]
    (dR dZ : R → ℕ) (dH : ∀ i, H i → ℕ)
    (hHsum : ∀ i, ∑ h : H i, dH i h ≤ dR i)
    (hRsum : ∑ i, dR i ≤ targetDY)
    (hZ : ∀ i, dZ i ≤ targetDZ) :
    ∑ p : Σ i, H i,
        2 * targetDX * (dR p.1 + 1) * dH p.1 p.2 * dZ p.1 ≤
      2 * targetDX * (targetDY ^ 2 + targetDY) * targetDZ := by
  classical
  rw [Fintype.sum_sigma]
  calc
    ∑ i, ∑ h : H i, 2 * targetDX * (dR i + 1) * dH i h * dZ i ≤
        ∑ i, 2 * targetDX * (dR i + 1) * dR i * dZ i := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (hHsum i)
    _ ≤ ∑ i, 2 * targetDX * (targetDY + 1) * dR i * targetDZ := by
      apply Finset.sum_le_sum
      intro i _
      have hRi : dR i ≤ targetDY :=
        (Finset.single_le_sum (fun j _ => Nat.zero_le (dR j)) (Finset.mem_univ i)).trans hRsum
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.add_le_add_right hRi 1)) le_rfl) (hZ i)
    _ = 2 * targetDX * (targetDY + 1) * targetDZ * ∑ i, dR i := by
      rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * targetDX * (targetDY + 1) * targetDZ * targetDY :=
      Nat.mul_le_mul_left _ hRsum
    _ = 2 * targetDX * (targetDY ^ 2 + targetDY) * targetDZ := by ring

/-- The degree-one endpoint is sent through the quadratic theorem.  This costs at most one
additional unit of `dH*dZ` for each surface; aggregating it still gives a quadratic `DY`
bound. -/
theorem improved_factor_degree_sum_with_linear_penalty
    {R : Type} [Fintype R] (H : R → Type)
    [∀ i, Fintype (H i)]
    (dR dZ : R → ℕ) (dH : ∀ i, H i → ℕ)
    (hHsum : ∀ i, ∑ h : H i, dH i h ≤ dR i)
    (hRsum : ∑ i, dR i ≤ targetDY)
    (hZ : ∀ i, dZ i ≤ targetDZ) :
    ∑ p : Σ i, H i,
        2 * targetDX * (dR p.1 + 1 + (if dR p.1 = 1 then 1 else 0)) *
          dH p.1 p.2 * dZ p.1 ≤
      2 * targetDX * (targetDY ^ 2 + 2 * targetDY) * targetDZ := by
  classical
  rw [Fintype.sum_sigma]
  calc
    ∑ i, ∑ h : H i,
          2 * targetDX * (dR i + 1 + (if dR i = 1 then 1 else 0)) *
            dH i h * dZ i ≤
        ∑ i, 2 * targetDX * (dR i + 2) * dR i * dZ i := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ∑ h : H i,
            2 * targetDX * (dR i + 1 + (if dR i = 1 then 1 else 0)) *
              dH i h * dZ i =
            (2 * targetDX * (dR i + 1 + (if dR i = 1 then 1 else 0)) * dZ i) *
              ∑ h : H i, dH i h := by
                rw [← Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro h _
                ring
        _ ≤ (2 * targetDX * (dR i + 1 +
              (if dR i = 1 then 1 else 0)) * dZ i) * dR i :=
          Nat.mul_le_mul_left _ (hHsum i)
        _ ≤ (2 * targetDX * (dR i + 2) * dZ i) * dR i := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _ (by split_ifs <;> omega)))
        _ = 2 * targetDX * (dR i + 2) * dR i * dZ i := by ring
    _ ≤ ∑ i, 2 * targetDX * (targetDY + 2) * dR i * targetDZ := by
      apply Finset.sum_le_sum
      intro i _
      have hRi : dR i ≤ targetDY :=
        (Finset.single_le_sum (fun j _ ⇒ Nat.zero_le (dR j))
          (Finset.mem_univ i)).trans hRsum
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.add_le_add_right hRi 2)) le_rfl)
        (hZ i)
    _ = 2 * targetDX * (targetDY + 2) * targetDZ * ∑ i, dR i := by
      rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * targetDX * (targetDY + 2) * targetDZ * targetDY :=
      Nat.mul_le_mul_left _ hRsum
    _ = 2 * targetDX * (targetDY ^ 2 + 2 * targetDY) * targetDZ := by ring

/-- Positive specialized factors are no more numerous than their total `Y` degree. -/
theorem factor_pair_card_le_degree
    {R : Type} [Fintype R] (H : R → Type)
    [∀ i, Fintype (H i)]
    (dR : R → ℕ) (dH : ∀ i, H i → ℕ)
    (hHpos : ∀ i h, 0 < dH i h)
    (hHsum : ∀ i, ∑ h : H i, dH i h ≤ dR i)
    (hRsum : ∑ i, dR i ≤ targetDY) :
    Fintype.card (Σ i, H i) ≤ targetDY := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ i, Fintype.card (H i) = ∑ i, ∑ _h : H i, 1 := by simp
    _ ≤ ∑ i, ∑ h : H i, dH i h := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun h _ => hHpos i h
    _ ≤ ∑ i, dR i := Finset.sum_le_sum fun i _ => hHsum i
    _ ≤ targetDY := hRsum

/-- Complete improved bookkeeping, including a separate `Y`-content exceptional set. -/
theorem bad_card_le_of_factor_cells
    {F R : Type} [Fintype F] [DecidableEq F] [Fintype R]
    (H : R → Type) [∀ i, Fintype (H i)]
    (bad content : Finset F) (cell : (Σ i, H i) → Finset F)
    (dR dZ : R → ℕ) (dH : ∀ i, H i → ℕ)
    (hcover : bad ⊆ content ∪ Finset.univ.biUnion cell)
    (hcontent : content.card ≤ targetDZ)
    (hcell : ∀ p, (cell p).card ≤
      2 * targetDX * (dR p.1 + 1) * dH p.1 p.2 * dZ p.1 + targetN)
    (hHpos : ∀ i h, 0 < dH i h)
    (hHsum : ∀ i, ∑ h : H i, dH i h ≤ dR i)
    (hRsum : ∑ i, dR i ≤ targetDY)
    (hZ : ∀ i, dZ i ≤ targetDZ) :
    bad.card ≤ targetDZ +
      2 * targetDX * (targetDY ^ 2 + targetDY) * targetDZ + targetN * targetDY := by
  classical
  calc
    bad.card ≤ content.card + ∑ p : Σ i, H i, (cell p).card :=
      card_le_content_add_sum_cells bad content cell hcover
    _ ≤ targetDZ + ∑ p : Σ i, H i,
        (2 * targetDX * (dR p.1 + 1) * dH p.1 p.2 * dZ p.1 + targetN) := by
      exact Nat.add_le_add hcontent (Finset.sum_le_sum fun p _ => hcell p)
    _ = targetDZ +
        (∑ p : Σ i, H i, 2 * targetDX * (dR p.1 + 1) * dH p.1 p.2 * dZ p.1) +
        targetN * Fintype.card (Σ i, H i) := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ targetDZ + 2 * targetDX * (targetDY ^ 2 + targetDY) * targetDZ +
        targetN * targetDY := by
      exact Nat.add_le_add
        (Nat.add_le_add_left
          (improved_factor_degree_sum H dR dZ dH hHsum hRsum hZ) targetDZ)
        (Nat.mul_le_mul_left targetN
        (factor_pair_card_le_degree H dR dH hHpos hHsum hRsum))

/-- Complete bookkeeping with the explicit degree-one quadraticization cost. -/
theorem bad_card_le_of_factor_cells_with_linear_penalty
    {F R : Type} [Fintype F] [DecidableEq F] [Fintype R]
    (H : R → Type) [∀ i, Fintype (H i)]
    (bad content : Finset F) (cell : (Σ i, H i) → Finset F)
    (dR dZ : R → ℕ) (dH : ∀ i, H i → ℕ)
    (hcover : bad ⊆ content ∪ Finset.univ.biUnion cell)
    (hcontent : content.card ≤ targetDZ)
    (hcell : ∀ p, (cell p).card ≤
      2 * targetDX * (dR p.1 + 1 + (if dR p.1 = 1 then 1 else 0)) *
        dH p.1 p.2 * dZ p.1 + targetN)
    (hHpos : ∀ i h, 0 < dH i h)
    (hHsum : ∀ i, ∑ h : H i, dH i h ≤ dR i)
    (hRsum : ∑ i, dR i ≤ targetDY)
    (hZ : ∀ i, dZ i ≤ targetDZ) :
    bad.card ≤ targetDZ +
      2 * targetDX * (targetDY ^ 2 + 2 * targetDY) * targetDZ +
        targetN * targetDY := by
  classical
  calc
    bad.card ≤ content.card + ∑ p : Σ i, H i, (cell p).card :=
      card_le_content_add_sum_cells bad content cell hcover
    _ ≤ targetDZ + ∑ p : Σ i, H i,
        (2 * targetDX * (dR p.1 + 1 + (if dR p.1 = 1 then 1 else 0)) *
          dH p.1 p.2 * dZ p.1 + targetN) := by
      exact Nat.add_le_add hcontent (Finset.sum_le_sum fun p _ ⇒ hcell p)
    _ = targetDZ +
        (∑ p : Σ i, H i,
          2 * targetDX * (dR p.1 + 1 + (if dR p.1 = 1 then 1 else 0)) *
            dH p.1 p.2 * dZ p.1) +
        targetN * Fintype.card (Σ i, H i) := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ targetDZ +
        2 * targetDX * (targetDY ^ 2 + 2 * targetDY) * targetDZ +
        targetN * targetDY := by
      exact Nat.add_le_add
        (Nat.add_le_add_left
          (improved_factor_degree_sum_with_linear_penalty H dR dZ dH
            hHsum hRsum hZ) targetDZ)
        (Nat.mul_le_mul_left targetN
          (factor_pair_card_le_degree H dR dH hHpos hHsum hRsum))

end FactorCounting

end ProximityPrize.SubmissionLower
