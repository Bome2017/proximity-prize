import ProximityPrize.SubmissionLower.Cap72Interpolation

namespace ProximityPrize.SubmissionLower.Cap72Root

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Cap72

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

noncomputable def specializeZ {F : Type*} [Field F] (z : F) (Q : TriPolynomial F) :
    Polynomial (Polynomial F) :=
  Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

noncomputable def composeAtSeed {F : Type*} [Field F]
    (Q : TriPolynomial F) (z : F) (p : Polynomial F) : Polynomial F :=
  (specializeZ z Q).eval p

lemma specializeZ_monomial {F : Type*} [Field F]
    (z a : F) (q : MonomialIndex) :
    specializeZ z (Cap72.monomial q a) =
      Polynomial.monomial (yDegree q)
        (Polynomial.monomial (xDegree q) (a * z ^ zDegree q)) := by
  simp [specializeZ, Cap72.monomial, Polynomial.map_monomial,
    Polynomial.eval_monomial]

lemma specializeZ_toPolynomial {F : Type*} [Field F]
    (z : F) (w : MonomialIndex → F) :
    specializeZ z (toPolynomial w) =
      ∑ q, Polynomial.monomial (yDegree q)
        (Polynomial.monomial (xDegree q) (w q * z ^ zDegree q)) := by
  classical
  unfold specializeZ toPolynomial
  change (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
      (∑ q, Cap72.monomial q (w q)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact specializeZ_monomial z (w q) q

lemma specializeZ_natWeightedDegree_le {F : Type*} [Field F]
    (z : F) (w : MonomialIndex → F) :
    Polynomial.Bivariate.natWeightedDegree (specializeZ z (toPolynomial w)) 1 131071 ≤
      1760955 := by
  classical
  rw [specializeZ_toPolynomial]
  refine (Polynomial.Bivariate.natWeightedDegree_sum_le Finset.univ
    (fun q => Polynomial.monomial (yDegree q)
      (Polynomial.monomial (xDegree q) (w q * z ^ zDegree q))) 1 131071).trans ?_
  apply Finset.sup_le
  intro q hq
  let a : F := w q * z ^ zDegree q
  have heq : Polynomial.monomial (yDegree q) (Polynomial.monomial (xDegree q) a) =
      a • Polynomial.Bivariate.monomial (xDegree q) (yDegree q) := by
    ext b x
    by_cases hb : yDegree q = b <;> by_cases hx : xDegree q = x <;>
      simp [Polynomial.Bivariate.monomial, Polynomial.coeff_monomial, hb, hx]
  rw [heq]
  refine (Polynomial.Bivariate.natWeightedDegree_smul_le a
    (Polynomial.Bivariate.monomial (F := F) (xDegree q) (yDegree q)) 1 131071).trans ?_
  rw [Polynomial.Bivariate.natWeightedDegree_monomial]
  have hw := weightedDegree_lt q
  norm_num at *
  omega

lemma composeAtSeed_natDegree_le {F : Type*} [Field F]
    (z : F) (w : MonomialIndex → F) (p : Polynomial F)
    (hp : p.natDegree ≤ 131071) :
    (composeAtSeed (toPolynomial w) z p).natDegree ≤ 1760955 := by
  unfold composeAtSeed
  exact (Polynomial.Bivariate.degree_eval_le_weightedDegree
    (specializeZ z (toPolynomial w)) p 131072 (by simpa using hp)).trans
      (specializeZ_natWeightedDegree_le z w)

lemma coeff_affine_binomial_term {F : Type*} [Field F]
    (u v : F) (r j ell : Nat) :
    (((Polynomial.C v * Polynomial.X) ^ j * Polynomial.C u ^ (r - j))).coeff ell =
      if ell = j then v ^ j * u ^ (r - j) else 0 := by
  rw [mul_pow, ← Polynomial.C_pow, ← Polynomial.C_pow, mul_assoc,
    Polynomial.X_pow_mul_C, ← mul_assoc, ← Polynomial.C_mul,
    Polynomial.coeff_C_mul_X_pow]

lemma coeff_C_add_C_mul_X_pow {F : Type*} [Field F]
    (u v : F) (r ell : Nat) :
    ((Polynomial.C u + Polynomial.C v * Polynomial.X) ^ r).coeff ell =
      affinePowerCoeff u v r ell := by
  rw [add_comm, (Commute.all (Polynomial.C v * Polynomial.X) (Polynomial.C u)).add_pow]
  change (Polynomial.lcoeff F ell)
      (∑ m ∈ Finset.range (r + 1),
        (Polynomial.C v * Polynomial.X) ^ m * Polynomial.C u ^ (r - m) *
          (r.choose m : Polynomial F)) = _
  rw [map_sum]
  unfold affinePowerCoeff
  by_cases hle : ell ≤ r
  · rw [if_pos hle]
    rw [Finset.sum_eq_single ell]
    · rw [Polynomial.lcoeff_apply, ← Polynomial.C_eq_natCast, coeff_mul_C,
        coeff_affine_binomial_term]
      simp
      ring
    · intro j hj hje
      have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
      rw [Polynomial.lcoeff_apply, ← Polynomial.C_eq_natCast, coeff_mul_C,
        coeff_affine_binomial_term]
      simp [hje.symm]
    · intro hell
      exact (hell (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))).elim
  · rw [if_neg hle]
    apply Finset.sum_eq_zero
    intro j hj
    have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
    have hne : j ≠ ell := by omega
    rw [Polynomial.lcoeff_apply, ← Polynomial.C_eq_natCast, coeff_mul_C,
      coeff_affine_binomial_term]
    simp [hne.symm]

noncomputable def shiftedAffinePower {F : Type*} [Field F]
    (u v : F) (r c : Nat) : Polynomial F :=
  ∑ ell : Fin 73, Polynomial.monomial ell.val
    (affinePowerCoeff u v r (ell.val - c) * if c ≤ ell.val then 1 else 0)

lemma coeff_univ_sum {F ι : Type*} [Semiring F] [Fintype ι]
    (f : ι → Polynomial F) (n : Nat) :
    (∑ i, f i).coeff n = ∑ i, (f i).coeff n := by
  change (Polynomial.lcoeff F n) (∑ i, f i) = _
  exact map_sum (Polynomial.lcoeff F n) f Finset.univ

lemma shiftedAffinePower_eq {F : Type*} [Field F]
    (u v : F) (r c : Nat) (hrc : r + c ≤ 72) :
    shiftedAffinePower u v r c =
      (Polynomial.C u + Polynomial.C v * Polynomial.X) ^ r * Polynomial.X ^ c := by
  classical
  ext ell
  rw [Polynomial.coeff_mul_X_pow']
  by_cases h73 : ell < 73
  · let e : Fin 73 := ⟨ell, h73⟩
    rw [show (shiftedAffinePower u v r c).coeff ell =
        (shiftedAffinePower u v r c).coeff e.val by rfl]
    unfold shiftedAffinePower
    rw [coeff_univ_sum]
    rw [Finset.sum_eq_single e]
    · rw [Polynomial.coeff_monomial_same]
      by_cases hc : c ≤ ell
      · rw [if_pos hc, mul_one, if_pos hc, coeff_C_add_C_mul_X_pow]
      · rw [if_neg hc, mul_zero, if_neg hc]
    · intro j hj hje
      rw [Polynomial.coeff_monomial_of_ne]
      exact Fin.val_ne_of_ne hje.symm
    · exact fun h => (h (Finset.mem_univ e)).elim
  · have hell : 72 < ell := by omega
    have hrlt : r + c < ell := lt_of_le_of_lt hrc (by omega)
    have hleft : (shiftedAffinePower u v r c).coeff ell = 0 := by
      unfold shiftedAffinePower
      rw [coeff_univ_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_monomial_of_ne]
      omega
    rw [hleft]
    by_cases hc : c ≤ ell
    · rw [if_pos hc, coeff_C_add_C_mul_X_pow]
      unfold affinePowerCoeff
      rw [if_neg]
      omega
    · rw [if_neg hc]

noncomputable def directAffineHasse {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (i : IRSProfile.Index) (d : DerivativeIndex) :
    Polynomial F :=
  ∑ q, if hs : d.1.val ≤ xDegree q then
    if ht : d.2.val ≤ yDegree q then
      Polynomial.C (w q * (Nat.choose (xDegree q) d.1.val : F) *
        (Nat.choose (yDegree q) d.2.val : F) *
        domain i ^ (xDegree q - d.1.val)) *
      (Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X) ^
          (yDegree q - d.2.val) *
        Polynomial.X ^ zDegree q
    else 0 else 0

lemma affineHassePolynomial_eq_direct {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (i : IRSProfile.Index) (d : DerivativeIndex) :
    affineHassePolynomial domain u v w i d = directAffineHasse domain u v w i d := by
  classical
  unfold affineHassePolynomial directAffineHasse
  simp_rw [constraintMap_apply]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hs : d.1.val ≤ xDegree q
  · by_cases ht : d.2.val ≤ yDegree q
    · simp only [constraintScalar, hs, ht, dif_pos]
      let K : F := w q * (Nat.choose (xDegree q) d.1.val : F) *
        (Nat.choose (yDegree q) d.2.val : F) *
        domain i ^ (xDegree q - d.1.val)
      have hcap : (yDegree q - d.2.val) + zDegree q ≤ 72 := by
        have hqcap := zDegree_add_yDegree_le q
        omega
      trans Polynomial.C K * shiftedAffinePower (u i) (v i)
        (yDegree q - d.2.val) (zDegree q)
      · unfold shiftedAffinePower K
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell hell
        rw [Polynomial.C_mul_monomial]
        congr 1
        ring
      · rw [shiftedAffinePower_eq (u i) (v i)
          (yDegree q - d.2.val) (zDegree q) hcap]
        simp only [K]
        ring
    · simp [constraintScalar, hs, ht]
  · simp [constraintScalar, hs]

lemma bivariate_coeff_shift_monomial {F : Type*} [Field F]
    (A x y : F) (a b s t : Nat) :
    Polynomial.Bivariate.coeff
      (Polynomial.Bivariate.shift
        (Polynomial.monomial b (Polynomial.monomial a A)) x y) s t =
      if hs : s ≤ a then if ht : t ≤ b then
        (Nat.choose a s : F) * (Nat.choose b t : F) *
          x ^ (a - s) * y ^ (b - t) * A
      else 0 else 0 := by
  unfold Polynomial.Bivariate.coeff Polynomial.Bivariate.shift
  rw [Polynomial.coeff_map]
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  change ((Polynomial.taylor x
    ((Nat.choose b t : Polynomial F) * Polynomial.monomial a A *
      Polynomial.C y ^ (b - t))).coeff s) = _
  rw [← Polynomial.C_eq_natCast]
  simp only [Polynomial.taylor_mul, Polynomial.taylor_C,
    Polynomial.taylor_pow]
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
    Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial,
    Polynomial.eval_monomial]
  by_cases hs : s ≤ a
  · by_cases ht : t ≤ b
    · simp [hs, ht]
      ring
    · have hbt : b < t := Nat.lt_of_not_ge ht
      rw [Nat.choose_eq_zero_of_lt hbt]
      simp [hs, ht]
  · have has : a < s := Nat.lt_of_not_ge hs
    rw [Nat.choose_eq_zero_of_lt has]
    simp [hs]

noncomputable def shiftCoeffLinear {F : Type*} [Field F]
    (x y : F) (s t : Nat) : Polynomial (Polynomial F) →ₗ[F] F where
  toFun f := Polynomial.Bivariate.coeff (Polynomial.Bivariate.shift f x y) s t
  map_add' f g := by simp [Polynomial.Bivariate.shift, Polynomial.Bivariate.coeff]
  map_smul' a f := by simp [Polynomial.Bivariate.shift, Polynomial.Bivariate.coeff]

lemma bivariate_coeff_shift_sum {F ι : Type*} [Field F] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial (Polynomial F))
    (x y : F) (s t : Nat) :
    Polynomial.Bivariate.coeff
      (Polynomial.Bivariate.shift (∑ q ∈ S, f q) x y) s t =
      ∑ q ∈ S, Polynomial.Bivariate.coeff (Polynomial.Bivariate.shift (f q) x y) s t := by
  classical
  change shiftCoeffLinear x y s t (∑ q ∈ S, f q) =
    ∑ q ∈ S, shiftCoeffLinear x y s t (f q)
  rw [map_sum]

lemma eval_univ_sum {F ι : Type*} [Field F] [Fintype ι]
    (z : F) (f : ι → Polynomial F) :
    Polynomial.eval z (∑ q, f q) = ∑ q, Polynomial.eval z (f q) := by
  change (Polynomial.evalRingHom z) (∑ q, f q) = _
  exact map_sum (Polynomial.evalRingHom z) f Finset.univ

lemma shifted_specialize_coeff_eq_eval_direct {F : Type*} [Field F]
    (domain : IRSProfile.Index → F) (u v : IRSProfile.Index → F)
    (w : MonomialIndex → F) (z : F) (i : IRSProfile.Index) (d : DerivativeIndex) :
    Polynomial.Bivariate.coeff
      (Polynomial.Bivariate.shift (specializeZ z (toPolynomial w))
        (domain i) (u i + z * v i)) d.1.val d.2.val =
      Polynomial.eval z (directAffineHasse domain u v w i d) := by
  classical
  rw [specializeZ_toPolynomial]
  rw [show (∑ q, Polynomial.monomial (yDegree q)
      (Polynomial.monomial (xDegree q) (w q * z ^ zDegree q))) =
      ∑ q ∈ Finset.univ, Polynomial.monomial (yDegree q)
        (Polynomial.monomial (xDegree q) (w q * z ^ zDegree q)) by simp]
  rw [bivariate_coeff_shift_sum]
  unfold directAffineHasse
  rw [eval_univ_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [bivariate_coeff_shift_monomial]
  by_cases hs : d.1.val ≤ xDegree q
  · by_cases ht : d.2.val ≤ yDegree q
    · simp only [hs, ht, dif_pos, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      rw [Polynomial.eval_pow]
      simp
      ring
    · simp [hs, ht, Nat.choose_eq_zero_of_lt]
  · simp [hs, Nat.choose_eq_zero_of_lt]

/-- If all coefficients of total degree below `m` vanish and `P(0)=0`, then
`X^m` divides the evaluation.  This is the local form needed by the capped
interpolation argument. -/
lemma dvd_eval_of_total_coeff_zero {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (m : Nat)
    (hQ : ∀ i j, i + j < m → Polynomial.Bivariate.coeff Q i j = 0)
    (hP : P.coeff 0 = 0) :
    Polynomial.X ^ m ∣ Q.eval P := by
  have h_div_Pj : ∀ j : Nat, Polynomial.X ^ j ∣ P ^ j := fun j =>
    pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hP) j
  have h_div_term_all : ∀ i j : Nat, (Q.coeff j).coeff i ≠ 0 →
      Polynomial.X ^ m ∣
        Polynomial.monomial i ((Q.coeff j).coeff i) * P ^ j := by
    intro i j hij
    have h_div_term : Polynomial.X ^ (i + j) ∣
        Polynomial.monomial i ((Q.coeff j).coeff i) * P ^ j := by
      simp only [pow_add]
      exact mul_dvd_mul (by simp [← Polynomial.C_mul_X_pow_eq_monomial]) (h_div_Pj j)
    exact dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt fun h => hij (hQ i j h))) h_div_term
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine Finset.dvd_sum fun n hn => ?_
  rw [(Q.coeff n).as_sum_range_C_mul_X_pow]
  simp only [Finset.sum_mul, Polynomial.C_mul_X_pow_eq_monomial]
  classical
  exact Finset.dvd_sum fun i hi =>
    if hi0 : (Q.coeff n).coeff i = 0 then by simp [hi0]
    else h_div_term_all i n hi0

lemma eval_shifted_eq_shifted_eval {F : Type*} [Field F]
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (x y : F) :
    let Qsh := (Q.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).map
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C x))
    let Psh := P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y
    Qsh.eval Psh = (Q.eval P).comp (Polynomial.X + Polynomial.C x) := by
  induction Q using Polynomial.induction_on <;> aesop

def HasOrderAt {F : Type*} [Field F]
    (Q : Polynomial (Polynomial F)) (x y : F) (m : Nat) : Prop :=
  ∀ i j, i + j < m →
    Polynomial.Bivariate.coeff (Polynomial.Bivariate.shift Q x y) i j = 0

lemma orderAt_eval_ge {F : Type*} [Field F] [DecidableEq F]
    (Q : Polynomial (Polynomial F)) (P : Polynomial F) (x : F) (m : Nat)
    (h : HasOrderAt Q x (P.eval x) m) :
    Q.eval P = 0 ∨ m ≤ (Q.eval P).rootMultiplicity x := by
  let Qsh := (Q.comp (Polynomial.X + Polynomial.C (Polynomial.C (P.eval x)))).map
    (Polynomial.compRingHom (Polynomial.X + Polynomial.C x))
  let Psh := P.comp (Polynomial.X + Polynomial.C x) - Polynomial.C (P.eval x)
  have hXm : Polynomial.X ^ m ∣ Qsh.eval Psh := by
    classical
    apply dvd_eval_of_total_coeff_zero
    · exact h
    · simp +zetaDelta at *
      simp [Polynomial.coeff_zero_eq_eval_zero]
  have hshift : Qsh.eval Psh = (Q.eval P).comp
      (Polynomial.X + Polynomial.C x) := by
    convert eval_shifted_eq_shifted_eval Q P x (P.eval x) using 1
  have hXm' : Polynomial.X ^ m ∣ (Q.eval P).comp
      (Polynomial.X + Polynomial.C x) := hshift ▸ hXm
  have hdiv : (Polynomial.X - Polynomial.C x) ^ m ∣ Q.eval P :=
    Polynomial.X_sub_C_pow_dvd_iff.mpr hXm'
  by_cases hzero : Q.eval P = 0
  · exact Or.inl hzero
  · exact Or.inr ((Polynomial.le_rootMultiplicity_iff hzero).mpr hdiv)

lemma hasOrderAt_nine_of_interpolant {F : Type*} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) (z : F) (i : IRSProfile.Index) :
    HasOrderAt (specializeZ z Q.polynomial)
      (domain i) (u i + z * v i) 9 := by
  intro s t hst
  have hs9 : s < 9 := by omega
  have ht : t < 9 - s := by omega
  let d : DerivativeIndex := ⟨⟨s, hs9⟩, ⟨t, ht⟩⟩
  have hz : affineHassePolynomial domain u v Q.coefficients i d = 0 :=
    Q.affineMultiplicityNine i d
  have hrel : Polynomial.Bivariate.coeff
      (Polynomial.Bivariate.shift (specializeZ z (toPolynomial Q.coefficients))
        (domain i) (u i + z * v i)) d.1.val d.2.val = 0 := by
    rw [shifted_specialize_coeff_eq_eval_direct domain u v Q.coefficients z i d]
    rw [← affineHassePolynomial_eq_direct, hz, Polynomial.eval_zero]
  simpa [Interpolant.polynomial, d] using hrel

lemma matched_rootMultiplicity_nine {F : Type*} [Field F] [DecidableEq F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) (z : F) (p : Polynomial F)
    (i : IRSProfile.Index) (hmatch : p.eval (domain i) = u i + z * v i) :
    composeAtSeed Q.polynomial z p = 0 ∨
      9 ≤ (composeAtSeed Q.polynomial z p).rootMultiplicity (domain i) := by
  unfold composeAtSeed
  have horder := hasOrderAt_nine_of_interpolant Q z i
  have horder' : HasOrderAt (specializeZ z Q.polynomial)
      (domain i) (p.eval (domain i)) 9 := by
    simpa [hmatch] using horder
  exact orderAt_eval_ge (specializeZ z Q.polynomial) p (domain i) 9 horder'

lemma finset_mul_card_le_natDegree_of_rootMultiplicity_ge {F : Type*}
    [Field F] [DecidableEq F] (R : Polynomial F) (xs : Finset F) (m : Nat)
    (hmult : ∀ x, x ∈ xs → m ≤ R.rootMultiplicity x) :
    m * xs.card ≤ R.natDegree := by
  classical
  have hsum_le_roots : ∑ x ∈ xs, m ≤ R.roots.card := by
    calc
      ∑ x ∈ xs, m ≤ ∑ x ∈ xs, Multiset.count x R.roots := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [Polynomial.count_roots] using hmult x hx
      _ ≤ ∑ x ∈ xs ∪ R.roots.toFinset, Multiset.count x R.roots := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_union.mpr (Or.inl hx)
        · intro x hx hnot
          exact Nat.zero_le _
      _ = R.roots.card := by
        rw [Multiset.sum_count_eq_card]
        intro x hx
        exact Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hx))
  have hroots_le : R.roots.card ≤ R.natDegree := Polynomial.card_roots' R
  simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using
    le_trans hsum_le_roots hroots_le

theorem composeAtSeed_eq_zero_of_many_agreements {F : Type*} [Field F] [DecidableEq F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Interpolant domain u v) (z : F) (p : Polynomial F)
    (hpdeg : p.natDegree ≤ 131071)
    (A : Finset IRSProfile.Index) (hAcard : 196592 ≤ A.card)
    (hdomain : Function.Injective domain)
    (hagree : ∀ i ∈ A, p.eval (domain i) = u i + z * v i) :
    composeAtSeed Q.polynomial z p = 0 := by
  classical
  let R := composeAtSeed Q.polynomial z p
  by_contra hR
  have hRne : R ≠ 0 := hR
  let xs : Finset F := A.image domain
  have hxs : xs.card = A.card := Finset.card_image_of_injective A hdomain
  have hmult : ∀ x, x ∈ xs → 9 ≤ R.rootMultiplicity x := by
    intro x hx
    obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hx
    have hm := matched_rootMultiplicity_nine Q z p i (hagree i hiA)
    exact hm.resolve_left hRne
  have hroots : 9 * A.card ≤ R.natDegree := by
    rw [← hxs]
    exact finset_mul_card_le_natDegree_of_rootMultiplicity_ge R xs 9 hmult
  have hdeg : R.natDegree ≤ 1760955 := by
    exact composeAtSeed_natDegree_le z Q.coefficients p hpdeg
  omega

end ProximityPrize.SubmissionLower.Cap72Root
