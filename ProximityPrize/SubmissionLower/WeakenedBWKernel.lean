/-
  Defense-angle cut for the 5314 cell (65552).

  ArkLib's GoodCoeffs determinant lemma
  `RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt`
  takes a relUDR hypothesis, but inspects it only through two size facts
  (`e + deg ≤ n` and `e + 1 ≤ n`). Both survive at cell 65552. They are not
  the size facts the square-submatrix argument actually needs.

  The homogeneous BW matrix is `n × N` with `N = (e + 1) + (e + deg)`.
  The lemma quantifies over `Fin N ↪ ι`, which requires `N ≤ n`, i.e.
  `2e + deg + 1 ≤ n`. That fails by 33 at this cell — the same order as
  the classical `2e < d` failure of 31. RelUDR cannot be weakened to
  `e + deg ≤ n` without replacing the square-row embedding, and restoring
  tallness by puncturing `t ≥ 33` error positions explodes the existing
  `5^t` MCA union bound past `2⁻¹²⁸`.
-/

import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.WeakenedBWKernel

open ProximityPrize.Benchmark
open Code
open scoped NNReal

/-- Evaluation-domain length `2^18`. -/
def n : Nat := 2 ^ 18

/-- RS degree bound / base dimension `2^17`. -/
def deg : Nat := IRSProfile.baseDimension

/-- Hamming cell targeted by `ProtocolClaim 5314 262209 1048576`. -/
def e : Nat := 65552

/-- Column count of `BW_homMatrix e deg`. -/
def Ncols : Nat := (e + 1) + (e + deg)

/-- Classical RS min-distance form `n - deg + 1`. -/
def d : Nat := n - deg + 1

theorem n_eq_indexCard : n = Fintype.card IRSProfile.Index := by
  simp [n, IRSProfile.Index, Fintype.card_fin]

theorem deg_eq_baseDimension : deg = 2 ^ 17 := by
  simp [deg, IRSProfile.baseDimension]

theorem e_add_deg_le_n : e + deg ≤ n := by
  norm_num [e, deg, n, IRSProfile.baseDimension]

theorem e_add_one_le_n : e + 1 ≤ n := by
  norm_num [e, n]

/-- The *surviving* matrix-size facts at cell 65552. These are exactly the
two numeric consequences ArkLib extracts from relUDR in
`RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR` and
`RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR`. -/
theorem surviving_size_lemmas :
    e + deg ≤ n ∧ e + 1 ≤ n :=
  ⟨e_add_deg_le_n, e_add_one_le_n⟩

theorem d_eq : d = 131073 := by
  norm_num [d, n, deg, IRSProfile.baseDimension]

theorem two_e_not_lt_d : ¬ 2 * e < d := by
  norm_num [e, d, n, deg, IRSProfile.baseDimension]

theorem two_e_fails_by_31 : 2 * e - d = 31 := by
  norm_num [e, d, n, deg, IRSProfile.baseDimension]

/-- Tallness / squareness for the homogeneous BW matrix: `N ≤ n`. -/
theorem Ncols_eq : Ncols = 262177 := by
  norm_num [Ncols, e, deg, IRSProfile.baseDimension]

theorem Ncols_gt_n : n < Ncols := by
  norm_num [n, Ncols, e, deg, IRSProfile.baseDimension]

theorem tallness_deficit : Ncols - n = 33 := by
  norm_num [Ncols, n, e, deg, IRSProfile.baseDimension]

/-- The square-row embedding quantified by
`RS_BW_homMatrix_det_submatrix_eq_zero_of_goodCoeffs_card_gt` does not exist
at cell 65552, so that lemma cannot be instantiated no matter how relUDR is
weakened to `e + deg ≤ n`. -/
theorem no_square_row_embedding :
    IsEmpty (Fin Ncols ↪ IRSProfile.Index) := by
  refine ⟨fun f => ?_⟩
  have hle :
      Fintype.card (Fin Ncols) ≤ Fintype.card IRSProfile.Index :=
    Fintype.card_le_of_injective f f.injective
  have hlt : Fintype.card IRSProfile.Index < Fintype.card (Fin Ncols) := by
    simp [IRSProfile.Index, Fintype.card_fin]
    exact Ncols_gt_n
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hle hlt)

/-- 5314 operating radius used by the georgwiese reduction. -/
noncomputable def cellRadius : ℝ≥0 := (262209 : ℝ≥0) / 1048576

theorem cellRadius_floor :
    ⌊(cellRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 65552 := by
  norm_num [cellRadius, IRSProfile.Index]

end ProximityPrize.SubmissionLower.WeakenedBWKernel
