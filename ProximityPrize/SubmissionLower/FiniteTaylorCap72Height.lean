import ProximityPrize.SubmissionLower.FiniteTaylorExtraction

/-!
# Closed Cap72 Taylor height bounds

This module composes the structural quotient-degree estimate with the sharp
`q`-weighted forcing estimate, then closes the concrete Taylor recurrence.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorCap72Height

open Polynomial
open FiniteTaylorCore
open FiniteTaylorExtraction

noncomputable section

variable {F : Type*} [Field F]

/-- Cap72 forcing height with the quotient-variable degree discharged from
`h ≤ 11` and the outer relation degree bound. -/
theorem cap72_clearedTaylorForcing_height_le_auto
    (q : Polynomial F) (x₀ : F) (R : TriPolynomial F) (h : Nat)
    (Hbar : Polynomial (Polynomial F))
    (hh : 0 < h) (hh11 : h ≤ 11)
    (hHbar : Hbar.Monic) (hHdeg : Hbar.natDegree = h)
    (hHheight : polyHeight Hbar ≤ 792)
    (hqdeg : q.natDegree ≤ 400000)
    (hRdeg : R.natDegree ≤ 11)
    (hRheight : ∀ j, polyHeight ((shiftX x₀ R).coeff j) ≤ 864)
    (t : Nat) (history : Fin (t + 1) → Fin h → Polynomial F)
    (hzero : vectorHeight (history ⟨0, by omega⟩) ≤ 1000)
    (hpos : ∀ i, 0 < i.1 → vectorHeight (history i) ≤
      70100000 + (i.1 - 1) * 72000000) :
    vectorHeight (clearedTaylorForcing q x₀ R h Hbar t history) ≤
      70000000 + t * 72000000 := by
  apply cap72_clearedTaylorForcing_height_le q x₀ R h Hbar hh hHbar
    hHdeg hHheight hqdeg hRdeg hRheight
  · intro s hist
    refine (clearedNonlinearTaylorCoefficient_natDegree_le
      q x₀ R h s 11 hh hist hRdeg).trans ?_
    have hhpred : h - 1 ≤ 10 := by omega
    exact (Nat.mul_le_mul_left 11 hhpred).trans (by norm_num)
  · exact hzero
  · exact hpos

/-- Fully closed numerical height endpoint for the concrete Cap72 Taylor
numerators. -/
theorem cap72_concreteTaylorNumerators_height_le_10pow13
    (x₀ : F) (R : TriPolynomial F) (h : Nat)
    (Hbar J : Polynomial (Polynomial F)) (a0 : Fin h → Polynomial F)
    (hh : 0 < h) (hh11 : h ≤ 11)
    (hHbar : Hbar.Monic) (hHdeg : Hbar.natDegree = h)
    (hHheight : polyHeight Hbar ≤ 792)
    (hJdegree : J.natDegree ≤ 10) (hJheight : polyHeight J ≤ 864)
    (hRdeg : R.natDegree ≤ 11)
    (hRheight : ∀ j, polyHeight ((shiftX x₀ R).coeff j) ≤ 864)
    (ha0 : vectorHeight a0 ≤ 1000)
    (i : Nat) (hi : i ≤ 131071) :
    vectorHeight (concreteTaylorNumerators x₀ R h Hbar J a0 i) ≤
      10000000000000 := by
  have hqdeg : (multiplicationMatrix h Hbar J).det.natDegree ≤ 400000 :=
    cap72_multiplicationMatrix_det_natDegree_le_400000
      h Hbar J hh11 hHheight hJdegree hJheight
  apply cap72_concreteTaylorNumerators_height_le_10pow13_of_shifted_forcing
    x₀ R h Hbar J a0 hh11 hHheight hJdegree hJheight ha0
  · intro t history hzero hpos
    exact cap72_clearedTaylorForcing_height_le_auto
      (multiplicationMatrix h Hbar J).det x₀ R h Hbar hh hh11 hHbar
      hHdeg hHheight hqdeg hRdeg hRheight t history hzero hpos
  · exact hi

end

end ProximityPrize.SubmissionLower.FiniteTaylorCap72Height
