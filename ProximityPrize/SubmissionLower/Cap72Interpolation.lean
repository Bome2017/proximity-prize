import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.Cap72

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open Polynomial
open ProximityPrize.Benchmark

abbrev MonomialIndex := Sigma fun b : Fin 12 =>
  Fin (73 - b.val) × Fin (1760956 - 131071 * b.val)

abbrev DerivativeIndex := Sigma fun s : Fin 9 => Fin (9 - s.val)

abbrev ConstraintIndex := IRSProfile.Index × DerivativeIndex × Fin 73

abbrev TriPolynomial (F : Type*) [Semiring F] := Polynomial (Polynomial (Polynomial F))

def yDegree (q : MonomialIndex) : Nat := q.1.val
def zDegree (q : MonomialIndex) : Nat := q.2.1.val
def xDegree (q : MonomialIndex) : Nat := q.2.2.val

lemma yDegree_le (q : MonomialIndex) : yDegree q ≤ 11 := by
  exact Nat.le_pred_of_lt q.1.isLt

lemma zDegree_add_yDegree_le (q : MonomialIndex) : zDegree q + yDegree q ≤ 72 := by
  have hc := q.2.1.isLt
  have hb := q.1.isLt
  simp only [zDegree, yDegree] at *
  omega

lemma weightedDegree_lt (q : MonomialIndex) :
    xDegree q + 131071 * yDegree q < 1760956 := by
  have ha := q.2.2.isLt
  have hb := q.1.isLt
  simp only [xDegree, yDegree] at *
  omega

noncomputable def monomial {F : Type*} [Semiring F] (q : MonomialIndex) (a : F) :
    TriPolynomial F :=
  Polynomial.monomial (yDegree q)
    (Polynomial.monomial (xDegree q)
      (Polynomial.monomial (zDegree q) a))

noncomputable def toPolynomial {F : Type*} [Semiring F] (v : MonomialIndex → F) :
    TriPolynomial F :=
  ∑ q, monomial q (v q)

noncomputable def tripleCoeff {F : Type*} [Semiring F] (q : MonomialIndex) :
    TriPolynomial F →+ F :=
  (Polynomial.lcoeff F (zDegree q)).toAddMonoidHom.comp
    ((Polynomial.lcoeff (Polynomial F) (xDegree q)).toAddMonoidHom.comp
      (Polynomial.lcoeff (Polynomial (Polynomial F)) (yDegree q)).toAddMonoidHom)

@[simp] lemma tripleCoeff_apply {F : Type*} [Semiring F] (q : MonomialIndex)
    (p : TriPolynomial F) :
    tripleCoeff q p = (((p.coeff (yDegree q)).coeff (xDegree q)).coeff (zDegree q)) := rfl

lemma monomialIndex_ext {r q : MonomialIndex}
    (hb : yDegree r = yDegree q) (hc : zDegree r = zDegree q)
    (ha : xDegree r = xDegree q) : r = q := by
  rcases r with ⟨rb, rc, ra⟩
  rcases q with ⟨qb, qc, qa⟩
  simp only [yDegree, zDegree, xDegree] at hb hc ha
  have hb' : rb = qb := Fin.ext hb
  subst qb
  have hc' : rc = qc := Fin.ext hc
  subst qc
  have ha' : ra = qa := Fin.ext ha
  subst qa
  rfl

lemma coeff_monomial_eq {F : Type*} [Semiring F]
    (q r : MonomialIndex) (a : F) :
    (((monomial r a).coeff (yDegree q)).coeff (xDegree q)).coeff (zDegree q) =
      if r = q then a else 0 := by
  simp only [monomial, Polynomial.coeff_monomial]
  by_cases hb : yDegree r = yDegree q
  · simp only [hb, if_true]
    by_cases ha : xDegree r = xDegree q
    · simp only [ha, if_true]
      by_cases hc : zDegree r = zDegree q
      · have hrq : r = q := monomialIndex_ext hb hc ha
        simp [hrq]
      · have hrq : r ≠ q := fun h => hc (h ▸ rfl)
        rw [Polynomial.coeff_monomial_same]
        rw [Polynomial.coeff_monomial_of_ne _ (Ne.symm hc)]
        simp [hrq]
    · have hrq : r ≠ q := fun h => ha (h ▸ rfl)
      rw [Polynomial.coeff_monomial_of_ne _ (Ne.symm ha), Polynomial.coeff_zero]
      simp [hrq]
  · have hrq : r ≠ q := fun h => hb (h ▸ rfl)
    simp only [hb, if_false, Polynomial.coeff_zero, hrq]

lemma coeff_toPolynomial {F : Type*} [Semiring F] (v : MonomialIndex → F)
    (q : MonomialIndex) :
    ((((toPolynomial v).coeff (yDegree q)).coeff (xDegree q)).coeff (zDegree q)) = v q := by
  classical
  rw [← tripleCoeff_apply]
  rw [toPolynomial, map_sum]
  rw [Finset.sum_eq_single q]
  · rw [tripleCoeff_apply, coeff_monomial_eq]
    simp
  · intro r hr hrq
    rw [tripleCoeff_apply, coeff_monomial_eq, if_neg hrq]
  · exact fun h => (h (Finset.mem_univ q)).elim

lemma toPolynomial_ne_zero {F : Type*} [Semiring F] {v : MonomialIndex → F}
    (hv : v ≠ 0) : toPolynomial v ≠ 0 := by
  intro hp
  apply hv
  funext q
  have := coeff_toPolynomial v q
  rw [hp] at this
  simpa using this.symm

lemma toPolynomial_natDegree_le {F : Type*} [Semiring F] (v : MonomialIndex → F) :
    (toPolynomial v).natDegree ≤ 11 := by
  classical
  unfold toPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  exact (Polynomial.natDegree_monomial_le _).trans (yDegree_le q)

lemma monomial_natWeightedDegree_le {F : Type*} [Field F]
    (q : MonomialIndex) (a : F) :
    Polynomial.Bivariate.natWeightedDegree (monomial q a) 1 131071 ≤ 1760955 := by
  let za : Polynomial F := Polynomial.monomial (zDegree q) a
  have heq : monomial q a = za • Polynomial.Bivariate.monomial (xDegree q) (yDegree q) := by
    ext b x z
    by_cases hb : yDegree q = b
    · by_cases hx : xDegree q = x
      · simp [monomial, za, Polynomial.Bivariate.monomial,
          Polynomial.coeff_monomial, hb, hx]
      · simp [monomial, za, Polynomial.Bivariate.monomial,
          Polynomial.coeff_monomial, hb, hx]
    · simp [monomial, za, Polynomial.Bivariate.monomial,
        Polynomial.coeff_monomial, hb]
  rw [heq]
  refine (Polynomial.Bivariate.natWeightedDegree_smul_le za
    (Polynomial.Bivariate.monomial (F := Polynomial F) (xDegree q) (yDegree q))
    1 131071).trans ?_
  rw [Polynomial.Bivariate.natWeightedDegree_monomial]
  have := weightedDegree_lt q
  norm_num at *
  omega

lemma toPolynomial_natWeightedDegree_le {F : Type*} [Field F]
    (v : MonomialIndex → F) :
    Polynomial.Bivariate.natWeightedDegree (toPolynomial v) 1 131071 ≤ 1760955 := by
  classical
  unfold toPolynomial
  refine (Polynomial.Bivariate.natWeightedDegree_sum_le Finset.univ
    (fun q => monomial q (v q)) 1 131071).trans ?_
  apply Finset.sup_le
  intro q hq
  exact monomial_natWeightedDegree_le q (v q)

def derivativeOrder (d : DerivativeIndex) : Nat := d.1.val + d.2.val

lemma derivativeOrder_lt_nine (d : DerivativeIndex) : derivativeOrder d < 9 := by
  have := d.2.isLt
  simp only [derivativeOrder]
  omega

noncomputable def affinePowerCoeff {F : Type*} [Field F]
    (u v : F) (r ell : Nat) : F :=
  if ell ≤ r then (Nat.choose r ell : F) * u ^ (r - ell) * v ^ ell else 0

noncomputable def constraintScalar {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (q : MonomialIndex) (c : ConstraintIndex) : F :=
  let s := c.2.1.1.val
  let t := c.2.1.2.val
  let ell := c.2.2.val
  if hs : s ≤ xDegree q then
    if ht : t ≤ yDegree q then
      (Nat.choose (xDegree q) s : F) *
      (Nat.choose (yDegree q) t : F) *
      domain c.1 ^ (xDegree q - s) *
      affinePowerCoeff (u c.1) (v c.1) (yDegree q - t) (ell - zDegree q) *
      (if zDegree q ≤ ell then 1 else 0)
    else 0
  else 0

noncomputable def constraintMap {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F) :
    (MonomialIndex → F) →ₗ[F] (ConstraintIndex → F) where
  toFun w c := ∑ q, w q * constraintScalar domain u v q c
  map_add' a b := by
    funext c
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    funext c
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring

set_option maxRecDepth 10000000 in
lemma constraintMap_apply {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (c : ConstraintIndex) :
    constraintMap domain u v w c =
      ∑ q, w q * constraintScalar domain u v q c := by
  rfl

/-- The `(s,t)` Hasse specialization at the affine point
`(domain i, u i + Z * v i)`, represented by its exact coefficient formula.
The `ell`-th coefficient is one of the interpolation system's equations. -/
noncomputable def affineHassePolynomial {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (i : IRSProfile.Index) (d : DerivativeIndex) :
    Polynomial F :=
  ∑ ell : Fin 73,
    Polynomial.monomial ell.val ((constraintMap domain u v w) (i, d, ell))

lemma affineHassePolynomial_natDegree_le {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (i : IRSProfile.Index) (d : DerivativeIndex) :
    (affineHassePolynomial domain u v w i d).natDegree ≤ 72 := by
  classical
  unfold affineHassePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ell hell
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_pred_of_lt ell.isLt)

lemma affineHassePolynomial_eq_zero_of_mem_ker {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    {w : MonomialIndex → F} (hw : constraintMap domain u v w = 0)
    (i : IRSProfile.Index) (d : DerivativeIndex) :
    affineHassePolynomial domain u v w i d = 0 := by
  classical
  unfold affineHassePolynomial
  apply Finset.sum_eq_zero
  intro ell hell
  have h := congrFun hw (i, d, ell)
  simp only [Pi.zero_apply] at h
  rw [h, Polynomial.monomial_zero_right]

lemma card_monomialIndex : Fintype.card MonomialIndex = 861196208 := by
  simp only [MonomialIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

lemma card_derivativeIndex : Fintype.card DerivativeIndex = 45 := by
  simp only [DerivativeIndex, Fintype.card_sigma, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

lemma card_constraintIndex : Fintype.card ConstraintIndex = 861143040 := by
  simp only [ConstraintIndex, DerivativeIndex, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ, IRSProfile.Index]

lemma finrank_constraints_lt_coefficients (F : Type*) [Field F] :
    Module.finrank F (ConstraintIndex → F) < Module.finrank F (MonomialIndex → F) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    card_constraintIndex, card_monomialIndex]
  norm_num

theorem exists_kernel_vector {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F) :
    ∃ w : MonomialIndex → F, w ≠ 0 ∧ constraintMap domain u v w = 0 := by
  have hk : LinearMap.ker (constraintMap domain u v) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (finrank_constraints_lt_coefficients F)
  obtain ⟨w, hwker, hw0⟩ := (Submodule.ne_bot_iff _).mp hk
  exact ⟨w, hw0, hwker⟩

structure Interpolant {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F) where
  coefficients : MonomialIndex → F
  coefficients_ne_zero : coefficients ≠ 0
  constraints : constraintMap domain u v coefficients = 0

noncomputable def Interpolant.polynomial {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) : TriPolynomial F :=
  toPolynomial Q.coefficients

lemma Interpolant.polynomial_ne_zero {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) : Q.polynomial ≠ 0 :=
  toPolynomial_ne_zero Q.coefficients_ne_zero

lemma Interpolant.polynomial_natDegree_le {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) : Q.polynomial.natDegree ≤ 11 :=
  toPolynomial_natDegree_le Q.coefficients

lemma Interpolant.polynomial_natWeightedDegree_le {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) :
    Polynomial.Bivariate.natWeightedDegree Q.polynomial 1 131071 ≤ 1760955 :=
  toPolynomial_natWeightedDegree_le Q.coefficients

lemma Interpolant.affineMultiplicityNine {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) (i : IRSProfile.Index) (d : DerivativeIndex) :
    affineHassePolynomial domain u v Q.coefficients i d = 0 :=
  affineHassePolynomial_eq_zero_of_mem_ker domain u v Q.constraints i d

theorem exists_interpolant {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F) :
    Nonempty (Interpolant domain u v) := by
  obtain ⟨w, hw0, hwker⟩ := exists_kernel_vector domain u v
  exact ⟨⟨w, hw0, hwker⟩⟩

/-- Fixed-parameter capped symbolic GS interpolation.  It produces a nonzero
`F[Z][X][Y]` polynomial of Y-degree at most 11 and `(1,131071)` X/Y weighted
degree below 1760956.  Every coefficient index has `Z-degree + Y-degree ≤ 72`,
and all Hasse specializations of total order below nine vanish at every affine
word point. -/
theorem exists_cap72_interpolation {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F) :
    ∃ Q : Interpolant domain u v,
      Q.polynomial ≠ 0 ∧
      Q.polynomial.natDegree ≤ 11 ∧
      Polynomial.Bivariate.natWeightedDegree Q.polynomial 1 131071 ≤ 1760955 ∧
      (∀ q : MonomialIndex, zDegree q + yDegree q ≤ 72) ∧
      ∀ i : IRSProfile.Index, ∀ d : DerivativeIndex,
        affineHassePolynomial domain u v Q.coefficients i d = 0 := by
  let Q := Classical.choice (exists_interpolant domain u v)
  refine ⟨Q, Q.polynomial_ne_zero, Q.polynomial_natDegree_le,
    Q.polynomial_natWeightedDegree_le, ?_, Q.affineMultiplicityNine⟩
  exact zDegree_add_yDegree_le

end ProximityPrize.SubmissionLower.Cap72
