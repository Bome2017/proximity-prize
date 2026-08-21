import ProximityPrize.Benchmark.TargetLower

/-! Exploratory folded-DFT helper only. This module does not provide a Chen–Zhang
transport theorem or connect folded blocks to the active protocol certificate. -/

namespace ProximityPrize.SubmissionLower

open scoped BigOperators
open Polynomial

abbrev DFTField := ProximityPrize.Benchmark.IRSProfile.Field
abbrev Lane := Fin 16

/-- Interlace sixteen lane polynomials into one polynomial. -/
noncomputable def interlace16 (p : Lane → Polynomial DFTField) : Polynomial DFTField :=
  ∑ i : Lane, (Polynomial.X : Polynomial DFTField) ^ (i : Nat) *
    (p i).comp ((Polynomial.X : Polynomial DFTField) ^ 16)

/-- The blockwise length-sixteen DFT, including the usual `x^i` diagonal scaling. -/
noncomputable def laneDFT16 (ζ x : DFTField) (p : Lane → Polynomial DFTField) :
    Lane → DFTField := fun j =>
  ∑ i : Lane, (x ^ (i : Nat) * ζ ^ ((j : Nat) * (i : Nat))) *
    (p i).eval (x ^ 16)

/-- Evaluation of the interlaced polynomial on a sixteen-point multiplicative block is
exactly the blockwise DFT of the sixteen lane evaluations. -/
theorem interlace16_eval (ζ x : DFTField) (hζ : ζ ^ 16 = 1)
    (p : Lane → Polynomial DFTField) (j : Lane) :
    (interlace16 p).eval (x * ζ ^ (j : Nat)) = laneDFT16 ζ x p j := by
  simp only [interlace16, laneDFT16, eval_finset_sum, eval_mul, eval_pow, eval_X,
    eval_comp]
  apply Finset.sum_congr rfl
  intro i hi
  have hz : (ζ ^ (j : Nat)) ^ 16 = 1 := by
    calc
      (ζ ^ (j : Nat)) ^ 16 = ζ ^ ((j : Nat) * 16) := (pow_mul ζ _ _).symm
      _ = ζ ^ (16 * (j : Nat)) := by rw [Nat.mul_comm]
      _ = (ζ ^ 16) ^ (j : Nat) := pow_mul ζ _ _
      _ = 1 := by rw [hζ, one_pow]
  rw [mul_pow x (ζ ^ (j : Nat)) 16, hz, mul_one, mul_pow, pow_mul]

/-- Consequently replacement by the blockwise DFT preserves exact block equality.  This
is the metric isometry needed when Hamming distance counts whole sixteen-symbol blocks. -/
theorem foldedBlock_eq_iff_dftBlock_eq (ζ x : DFTField) (hζ : ζ ^ 16 = 1)
    (p q : Lane → Polynomial DFTField) :
    (fun j : Lane => (interlace16 p).eval (x * ζ ^ (j : Nat))) =
        (fun j : Lane => (interlace16 q).eval (x * ζ ^ (j : Nat))) ↔
      laneDFT16 ζ x p = laneDFT16 ζ x q := by
  simp_rw [interlace16_eval ζ x hζ]

end ProximityPrize.SubmissionLower
