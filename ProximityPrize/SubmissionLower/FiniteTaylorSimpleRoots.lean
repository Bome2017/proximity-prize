import ProximityPrize.SubmissionLower.FiniteTaylorCoprimeDet
import ProximityPrize.SubmissionLower.FiniteTaylorIntegralScale
import ProximityPrize.SubmissionLower.SequentialFactorSelection

namespace ProximityPrize.SubmissionLower.FiniteTaylorSimpleRoots

open Polynomial ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open FiniteTaylorCore FiniteTaylorIntegralScale

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

noncomputable section

/-- Specialize the coefficient variable without depending on the larger Taylor
extraction module.  This is definitionally the same coefficient map used
there. -/
def specializeZPoly (z : IRSProfile.Field)
    (P : Polynomial (Polynomial IRSProfile.Field)) :
    Polynomial IRSProfile.Field :=
  P.map (Polynomial.evalRingHom z)

/-- The fixed-size `Y`-resultant cutting out specializations where `H` acquires
a multiple root. -/
def simpleRootResultant (H : Polynomial (Polynomial IRSProfile.Field)) :
    Polynomial IRSProfile.Field :=
  Polynomial.resultant H H.derivative H.natDegree (H.natDegree - 1)

lemma irsField_natCast_ne_zero_of_pos_le_eleven
    {n : ℕ} (hn : 0 < n) (hle : n ≤ 11) :
    (n : IRSProfile.Field) ≠ 0 := by
  have hnbase : (n : KoalaBear.Field) ≠ 0 := by
    intro hzero
    have hdiv : KoalaBear.fieldSize ∣ n :=
      (CharP.cast_eq_zero_iff KoalaBear.Field KoalaBear.fieldSize n).mp hzero
    have hbig : KoalaBear.fieldSize ≤ n := Nat.le_of_dvd hn hdiv
    norm_num [KoalaBear.fieldSize] at hbig
    omega
  intro hzero
  have hcoeff := congrArg (fun a : IRSProfile.Field =>
    CompPoly.Extension.Ext.coeff a (0 : Fin 6)) hzero
  simp only [CompPoly.Extension.Ext.coeff_natCast,
    CompPoly.Extension.Ext.coeff_zero, Fin.val_zero, if_pos] at hcoeff
  exact hnbase hcoeff

lemma derivative_natDegree_eq_sub_one
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hpos : 0 < H.natDegree) (hle : H.natDegree ≤ 11) :
    H.derivative.natDegree = H.natDegree - 1 := by
  apply le_antisymm (Polynomial.natDegree_derivative_le H)
  apply Polynomial.le_natDegree_of_ne_zero
  have hncastF : (H.natDegree : IRSProfile.Field) ≠ 0 :=
    irsField_natCast_ne_zero_of_pos_le_eleven hpos hle
  have hncast : (H.natDegree : Polynomial IRSProfile.Field) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hncastF
  have hlead : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hpos)
  have hindex : H.natDegree - 1 + 1 = H.natDegree :=
    Nat.sub_add_cancel hpos
  rw [Polynomial.coeff_derivative]
  simpa only [hindex] using mul_ne_zero hlead hncast

/-- Fraction-field separability makes the exceptional resultant nonzero. -/
theorem simpleRootResultant_ne_zero
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hpos : 0 < H.natDegree) (hle : H.natDegree ≤ 11)
    (hsep : (SequentialFactorSelection.fractionMap H).Separable) :
    simpleRootResultant H ≠ 0 := by
  let K := FractionRing (Polynomial IRSProfile.Field)
  let φ : Polynomial IRSProfile.Field →+* K :=
    algebraMap (Polynomial IRSProfile.Field) K
  have hφinj : Function.Injective φ :=
    IsFractionRing.injective (Polynomial IRSProfile.Field) K
  have hdeg : (SequentialFactorSelection.fractionMap H).natDegree = H.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective hφinj H
  have hderivdeg :
      (SequentialFactorSelection.fractionMap H).derivative.natDegree =
        H.natDegree - 1 := by
    change (H.map φ).derivative.natDegree = H.natDegree - 1
    rw [Polynomial.derivative_map,
      Polynomial.natDegree_map_eq_of_injective hφinj]
    exact derivative_natDegree_eq_sub_one H hpos hle
  have hfieldRes : Polynomial.resultant
      (SequentialFactorSelection.fractionMap H)
      (SequentialFactorSelection.fractionMap H).derivative
      H.natDegree (H.natDegree - 1) ≠ 0 := by
    simpa [hdeg, hderivdeg] using Polynomial.resultant_ne_zero
      (SequentialFactorSelection.fractionMap H)
      (SequentialFactorSelection.fractionMap H).derivative hsep
  intro hzero
  apply hfieldRes
  change Polynomial.resultant (H.map φ) (H.map φ).derivative
    H.natDegree (H.natDegree - 1) = 0
  rw [Polynomial.derivative_map]
  rw [Polynomial.resultant_map_map]
  change φ (simpleRootResultant H) = 0
  simp [hzero]

lemma derivative_coeff_natDegree_le
    (H : Polynomial (Polynomial IRSProfile.Field)) {D : ℕ}
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ D) (i : ℕ) :
    (H.derivative.coeff i).natDegree ≤ D := by
  rw [Polynomial.coeff_derivative]
  change (H.coeff (i + 1) *
    Polynomial.C (((i + 1 : ℕ) : IRSProfile.Field))).natDegree ≤ D
  calc
    (H.coeff (i + 1) *
        Polynomial.C (((i + 1 : ℕ) : IRSProfile.Field))).natDegree ≤
        (H.coeff (i + 1)).natDegree +
          (Polynomial.C (((i + 1 : ℕ) : IRSProfile.Field)).natDegree) :=
      Polynomial.natDegree_mul_le
    _ ≤ D + 0 := Nat.add_le_add (hcoeff (i + 1)) (by
      rw [Polynomial.natDegree_C])
    _ = D := by simp

lemma natDegree_det_le_card_mul
    {F : Type*} [Field F] {N D : ℕ}
    (M : Matrix (Fin N) (Fin N) (Polynomial F))
    (hentry : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ N * D := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) •
        (∏ i : Fin N, M (σ i) i)).natDegree ≤
          (∏ i : Fin N, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  refine hsign.trans ((Polynomial.natDegree_prod_le
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => M (σ i) i)).trans ?_)
  calc
    ∑ i ∈ (Finset.univ : Finset (Fin N)), (M (σ i) i).natDegree
        ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)), D :=
          Finset.sum_le_sum fun i hi => hentry (σ i) i
    _ = N * D := by simp

lemma natDegree_resultant_le
    {F : Type*} [Field F]
    (f g : Polynomial (Polynomial F)) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (Polynomial.resultant f g m n).natDegree ≤ (m + n) * D := by
  unfold Polynomial.resultant
  apply natDegree_det_le_card_mul
  intro i j
  refine Fin.addCases ?_ ?_ j
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · simp
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · simp

/-- At Cap72 height and `Y`-degree, fewer than `1513` `Z`-values can create a
nonsimple root. -/
theorem simpleRootResultant_natDegree_le_1512
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hle : H.natDegree ≤ 11)
    (hcoeff : ∀ i, (H.coeff i).natDegree ≤ 72) :
    (simpleRootResultant H).natDegree ≤ 1512 := by
  have hraw := natDegree_resultant_le H H.derivative
    H.natDegree (H.natDegree - 1) 72 hcoeff
    (derivative_coeff_natDegree_le H hcoeff)
  dsimp [simpleRootResultant]
  omega

/-- Away from the resultant's roots, every root of the specialized `H` is
simple. -/
theorem derivative_eval_ne_zero_of_resultant_eval_ne_zero
    (H : Polynomial (Polynomial IRSProfile.Field))
    (z y : IRSProfile.Field) (hpos : 0 < H.natDegree)
    (hres : (simpleRootResultant H).eval z ≠ 0)
    (hroot : SequentialFactorSelection.evalZY z y H = 0) :
    SequentialFactorSelection.evalZY z y H.derivative ≠ 0 := by
  intro hderiv
  obtain ⟨p, q, _hp, _hq, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant H H.derivative
      (Nat.le_refl H.natDegree) (Polynomial.natDegree_derivative_le H)
      (Or.inl hpos.ne')
  have hev := congrArg
    (SequentialFactorSelection.evalZY z y) hbezout
  have hroot' : (H.map (Polynomial.evalRingHom z)).eval y = 0 := by
    simpa [SequentialFactorSelection.evalZY] using hroot
  have hderiv' : (H.derivative.map (Polynomial.evalRingHom z)).eval y = 0 := by
    simpa [SequentialFactorSelection.evalZY] using hderiv
  simp only [SequentialFactorSelection.evalZY, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.map_C, Polynomial.eval_C] at hev
  rw [hroot', hderiv'] at hev
  simp only [zero_mul, add_zero] at hev
  exact hres (by simpa [simpleRootResultant] using hev.symm)

/-- Fixed-degree resultants commute with specializing the coefficient variable.
The derivative is taken after specialization on the right. -/
theorem eval_simpleRootResultant
    (P : Polynomial (Polynomial IRSProfile.Field))
    (z : IRSProfile.Field) :
    (simpleRootResultant P).eval z =
      Polynomial.resultant (specializeZPoly z P) (specializeZPoly z P).derivative
        P.natDegree (P.natDegree - 1) := by
  change (Polynomial.evalRingHom z)
      (Polynomial.resultant P P.derivative P.natDegree
        (P.natDegree - 1)) = _
  rw [← Polynomial.resultant_map_map]
  simp only [specializeZPoly]
  rw [Polynomial.derivative_map]

/-- A nonvanishing fixed-degree resultant prevents the `Y`-degree from
dropping under specialization. -/
theorem specializeZ_natDegree_eq_of_simpleRootResultant_eval_ne_zero
    (P : Polynomial (Polynomial IRSProfile.Field))
    (z : IRSProfile.Field) (hpos : 0 < P.natDegree)
    (hres : (simpleRootResultant P).eval z ≠ 0) :
    (specializeZPoly z P).natDegree = P.natDegree := by
  apply le_antisymm
  · simpa [specializeZPoly] using
      (Polynomial.natDegree_map_le (p := P) (f := Polynomial.evalRingHom z))
  by_contra hnot
  have hlt : (specializeZPoly z P).natDegree < P.natDegree := by omega
  have hle : (specializeZPoly z P).natDegree ≤ P.natDegree - 1 := by omega
  have htop : (specializeZPoly z P).derivative.coeff (P.natDegree - 1) = 0 := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hpos]
    have hcoeff : (specializeZPoly z P).coeff P.natDegree = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hcoeff, zero_mul]
  apply hres
  rw [eval_simpleRootResultant]
  have hd : P.natDegree = (P.natDegree - 1) + 1 := by omega
  have hn : P.natDegree - 1 + 1 - 1 = P.natDegree - 1 := by omega
  rw [hd, hn]
  rw [Polynomial.resultant_succ_left_deg
    (f := specializeZPoly z P)
    (g := (specializeZPoly z P).derivative)
    (m := P.natDegree - 1) (n := P.natDegree - 1) hle]
  rw [htop, mul_zero]

end

end ProximityPrize.SubmissionLower.FiniteTaylorSimpleRoots
