/-
Pigeonhole det cut (new edge).

Prior defense files charged extra-row *cost* (5^k / 2^k) against FRI slack.
This file asks a different question about the BW kernel's first step:

  `RS_exists_nonzero_kernelVec_BW_homMatrix_of_goodCoeffs_card_gt`
  begins from `∀ r : Fin N → ι, det (M.submatrix r id) = 0`.

At cell 65552 one has N = 262177 > n = 2^18, so every
`r : Fin N → IRSProfile.Index` is non-injective. Every N×N row-submatrix
therefore has two equal rows and det = 0 as a polynomial — with no
relUDR hypothesis and no goodCoeffs card hypothesis.

The N×N-det step of the kernel theorem is free at this cell. What remains
is the Vandermonde/Schur construction, which only needs `e+deg ≤ n`
(already proved in WeakenedBWKernel / HBaseMCA).
-/

import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.PigeonDet

open ProximityPrize.Benchmark
open Matrix

/-- 5314 cell. -/
def e : Nat := 65552

def deg : Nat := IRSProfile.baseDimension

def n : Nat := 2 ^ 18

/-- Column count of `BW_homMatrix e deg`. -/
def Ncols : Nat := (e + 1) + (e + deg)

theorem n_eq_indexCard : n = Fintype.card IRSProfile.Index := by
  simp [n, IRSProfile.Index, Fintype.card_fin]

theorem deg_eq : deg = 2 ^ 17 := by
  simp [deg, IRSProfile.baseDimension]

theorem Ncols_eq : Ncols = 262177 := by
  norm_num [Ncols, e, deg, IRSProfile.baseDimension]

theorem Ncols_gt_n : n < Ncols := by
  norm_num [n, Ncols, e, deg, IRSProfile.baseDimension]

theorem e_add_deg_le_n : e + deg ≤ n := by
  norm_num [e, deg, n, IRSProfile.baseDimension]

/-- Every row-selection `Fin Ncols → Index` collides. -/
theorem row_map_not_injective
    (r : Fin Ncols → IRSProfile.Index) :
    ¬ Function.Injective r := by
  intro hf
  have hle :
      Fintype.card (Fin Ncols) ≤ Fintype.card IRSProfile.Index :=
    Fintype.card_le_of_injective r hf
  have hlt : Fintype.card IRSProfile.Index < Fintype.card (Fin Ncols) := by
    simp [IRSProfile.Index, Fintype.card_fin]
    exact Ncols_gt_n
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hle hlt)

/-- N×N dets vanish identically, no relUDR / no goodCoeffs. -/
theorem det_submatrix_zero
    {R : Type} [CommRing R]
    (M : Matrix IRSProfile.Index (Fin Ncols) R)
    (r : Fin Ncols → IRSProfile.Index) :
    Matrix.det (M.submatrix r id) = 0 := by
  have hni : ¬ Function.Injective r := row_map_not_injective r
  obtain ⟨i, j, hrij, hne⟩ := Function.not_injective_iff.mp hni
  refine Matrix.det_zero_of_row_eq (M := M.submatrix r id) hne ?_
  ext k
  simp [Matrix.submatrix_apply, hrij]

/-- Combined: kernel theorem's det obligation is discharged by cardinality. -/
theorem kernel_det_step_free
    {R : Type} [CommRing R]
    (M : Matrix IRSProfile.Index (Fin Ncols) R) :
    (∀ r : Fin Ncols → IRSProfile.Index,
        Matrix.det (M.submatrix r id) = 0) ∧
      e + deg ≤ n :=
  ⟨fun r => det_submatrix_zero M r, e_add_deg_le_n⟩

end ProximityPrize.SubmissionLower.PigeonDet
