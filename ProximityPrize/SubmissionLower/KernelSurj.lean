import Mathlib.LinearAlgebra.Matrix.Rank
import ProximityPrize.Benchmark.TargetLower

/-!
Rectangular rank-nullity kernel at cell 65552.

NEW ANGLE (not puncture, not 5^t defense, not extra-puncture budget, not
binary-cost rows, not N×N pigeonhole-det):

The BW homogeneous matrix is `Index × Fin Ncols` with
`Ncols = 262177 > #Index = 2^18`. Rank-nullity on the *rectangular*
map `mulVecLin A` gives a nonzero right kernel of dimension ≥ 33 —
with **no** `relUDR`, **no** `goodCoeffs`, **no** square minor, and
**no** `hδ`. Prior hops forced an `N×N` det (GoodCoeffs / pigeonhole).
That square never embeds into `Fin nEval`. The interpolating system is
already underdetermined by 33 columns.
-/

namespace ProximityPrize.SubmissionLower.KernelSurj

open ProximityPrize.Benchmark
open Matrix Module

variable {K : Type*} [Field K]

/-- More rows-than-columns fails: `#rows < #cols` ⇒ nontrivial right kernel. -/
theorem exists_nonzero_ker_of_card_lt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (h : Fintype.card ι < Fintype.card κ)
    (A : Matrix ι κ K) :
    ∃ v : κ → K, v ≠ 0 ∧ A *ᵥ v = 0 := by
  classical
  have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdom : finrank K (κ → K) = Fintype.card κ := finrank_pi K
  have hr : A.rank ≤ Fintype.card ι := A.rank_le_card_height
  have hnull :
      A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card κ := by
    simpa [Matrix.rank, hdom] using hsum
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro hb
    have : finrank K (LinearMap.ker A.mulVecLin) = 0 := by simp [hb]
    omega
  obtain ⟨v, hv, hvne⟩ :=
    (Submodule.ne_bot_iff (p := LinearMap.ker A.mulVecLin)).mp hker
  refine ⟨v, hvne, ?_⟩
  simpa [Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp hv)

def e : ℕ := 65552
def deg : ℕ := IRSProfile.baseDimension
def nEval : ℕ := 2 ^ 18
def Ncols : ℕ := (e + 1) + (e + deg)

theorem Ncols_eq : Ncols = 262177 := by
  norm_num [Ncols, e, deg, IRSProfile.baseDimension]

theorem nEval_eq_indexCard : nEval = Fintype.card IRSProfile.Index := by
  simp [nEval, IRSProfile.Index, Fintype.card_fin]

theorem nEval_lt_Ncols : nEval < Ncols := by
  norm_num [nEval, Ncols, e, deg, IRSProfile.baseDimension]

theorem indexCard_lt_Ncols :
    Fintype.card IRSProfile.Index < Fintype.card (Fin Ncols) := by
  simp [IRSProfile.Index, Fintype.card_fin]
  exact nEval_lt_Ncols

/-- Kernel dimension lower bound: nullity ≥ 33. -/
theorem ker_finrank_ge
    (A : Matrix IRSProfile.Index (Fin Ncols) K) :
    33 ≤ finrank K (LinearMap.ker A.mulVecLin) := by
  have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdom : finrank K (Fin Ncols → K) = Fintype.card (Fin Ncols) := finrank_pi K
  have hr : A.rank ≤ Fintype.card IRSProfile.Index := A.rank_le_card_height
  have hnull :
      A.rank + finrank K (LinearMap.ker A.mulVecLin) =
        Fintype.card (Fin Ncols) := by
    simpa [Matrix.rank, hdom] using hsum
  have hidx : Fintype.card IRSProfile.Index = nEval := nEval_eq_indexCard.symm
  have hN : Fintype.card (Fin Ncols) = Ncols := Fintype.card_fin _
  have : nEval + 33 = Ncols := by
    native_decide
  omega

/-- Every rectangular BW homogeneous matrix at this cell has a nonzero
    right kernel — no GoodCoeffs, no relUDR, no square det. -/
theorem bw_homMatrix_ker_free
    (A : Matrix IRSProfile.Index (Fin Ncols) K) :
    ∃ v : Fin Ncols → K, v ≠ 0 ∧ A *ᵥ v = 0 :=
  exists_nonzero_ker_of_card_lt indexCard_lt_Ncols A

end ProximityPrize.SubmissionLower.KernelSurj
