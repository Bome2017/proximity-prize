import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.FiniteTaylorCore

open scoped BigOperators
open Polynomial Matrix

noncomputable section

variable {F : Type*}

/-- Largest `Z`-degree among the coefficients of a polynomial in `T`. -/
def polyHeight [Semiring F] (P : Polynomial (Polynomial F)) : Nat :=
  P.support.sup fun i => (P.coeff i).natDegree

section PolynomialHeight

variable [Field F]

theorem natDegree_coeff_le_height (P : Polynomial (Polynomial F)) (i : Nat) :
    (P.coeff i).natDegree ≤ polyHeight P := by
  by_cases hi : P.coeff i = 0
  · simp [hi]
  · exact Finset.le_sup (f := fun j : Nat => (P.coeff j).natDegree)
      (Polynomial.mem_support_iff.mpr hi)

theorem polyHeight_le_iff {P : Polynomial (Polynomial F)} {D : Nat} :
    polyHeight P ≤ D ↔ ∀ i, (P.coeff i).natDegree ≤ D := by
  constructor
  · intro h i
    exact (natDegree_coeff_le_height P i).trans h
  · intro h
    exact (Finset.sup_le :
      (∀ i ∈ P.support, (P.coeff i).natDegree ≤ (D : Nat)) →
        P.support.sup (fun i => (P.coeff i).natDegree) ≤ D) (fun i _ => h i)

@[simp] theorem polyHeight_zero :
    polyHeight (0 : Polynomial (Polynomial F)) = 0 := by
  simp [polyHeight]

theorem polyHeight_add_le (P Q : Polynomial (Polynomial F)) :
    polyHeight (P + Q) ≤ max (polyHeight P) (polyHeight Q) := by
  rw [polyHeight_le_iff]
  intro i
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans
    (max_le_max (natDegree_coeff_le_height P i)
      (natDegree_coeff_le_height Q i))

theorem polyHeight_neg (P : Polynomial (Polynomial F)) :
    polyHeight (-P) = polyHeight P := by
  apply le_antisymm
  · rw [polyHeight_le_iff]
    intro i
    simpa only [coeff_neg, natDegree_neg] using natDegree_coeff_le_height P i
  · rw [polyHeight_le_iff]
    intro i
    simpa only [coeff_neg, neg_neg, natDegree_neg] using
      natDegree_coeff_le_height (-P) i

theorem polyHeight_mul_le (P Q : Polynomial (Polynomial F)) :
    polyHeight (P * Q) ≤ polyHeight P + polyHeight Q := by
  rw [polyHeight_le_iff]
  intro n
  rw [coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (natDegree_coeff_le_height P ij.1)
      (natDegree_coeff_le_height Q ij.2))

theorem polyHeight_pow_le (P : Polynomial (Polynomial F)) (n : Nat) :
    polyHeight (P ^ n) ≤ n * polyHeight P := by
  induction n with
  | zero =>
      rw [Nat.zero_mul, polyHeight_le_iff]
      intro i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [Polynomial.coeff_one, hi]
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (polyHeight_mul_le _ _).trans (Nat.add_le_add ih le_rfl)

theorem polyHeight_C (a : Polynomial F) :
    polyHeight (Polynomial.C a : Polynomial (Polynomial F)) = a.natDegree := by
  by_cases ha : a = 0
  · simp [ha, polyHeight]
  · simp [polyHeight, Polynomial.support_C, ha]

/-- The canonical representative in `(F[Z])[T]/(H)`. -/
def canonicalRemainder (H P : Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) := P %ₘ H

theorem canonicalRemainder_degree_lt {H : Polynomial (Polynomial F)}
    (hH : H.Monic) (P : Polynomial (Polynomial F)) :
    (canonicalRemainder H P).degree < H.degree :=
  Polynomial.degree_modByMonic_lt P hH

theorem canonicalRemainder_congruent {H : Polynomial (Polynomial F)}
    (P : Polynomial (Polynomial F)) :
    H ∣ canonicalRemainder H P - P :=
  Polynomial.dvd_modByMonic_sub P H

theorem canonicalRemainder_eq_self {H P : Polynomial (Polynomial F)}
    (hH : H.Monic) (hdeg : P.degree < H.degree) :
    canonicalRemainder H P = P :=
  (Polynomial.modByMonic_eq_self_iff hH).mpr hdeg

end PolynomialHeight

section MatrixHeight

variable [Field F]

/-- Largest degree of an entry of a square polynomial matrix. -/
def matrixHeight {n : Nat} (M : Matrix (Fin n) (Fin n) (Polynomial F)) : Nat :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => (M i j).natDegree

/-- Largest degree of an entry of a polynomial vector. -/
def vectorHeight {n : Nat} (v : Fin n → Polynomial F) : Nat :=
  Finset.univ.sup fun i => (v i).natDegree

theorem natDegree_vector_entry_le_vectorHeight {n : Nat}
    (v : Fin n → Polynomial F) (i : Fin n) :
    (v i).natDegree ≤ vectorHeight v := by
  exact Finset.le_sup (f := fun i : Fin n => (v i).natDegree) (Finset.mem_univ i)

theorem vectorHeight_le_iff {n D : Nat} {v : Fin n → Polynomial F} :
    vectorHeight v ≤ D ↔ ∀ i, (v i).natDegree ≤ D := by
  constructor
  · intro h i
    exact (natDegree_vector_entry_le_vectorHeight v i).trans h
  · intro h
    exact Finset.sup_le fun i _ => h i

theorem natDegree_entry_le_matrixHeight {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F)) (i j : Fin n) :
    (M i j).natDegree ≤ matrixHeight M := by
  exact (Finset.le_sup (f := fun j : Fin n => (M i j).natDegree)
      (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i : Fin n =>
      Finset.univ.sup fun j => (M i j).natDegree) (Finset.mem_univ i))

theorem matrixHeight_le_iff {n D : Nat}
    {M : Matrix (Fin n) (Fin n) (Polynomial F)} :
    matrixHeight M ≤ D ↔ ∀ i j, (M i j).natDegree ≤ D := by
  constructor
  · intro h i j
    exact (natDegree_entry_le_matrixHeight M i j).trans h
  · intro h
    apply Finset.sup_le
    intro i hi
    apply Finset.sup_le
    intro j hj
    exact h i j

@[simp] theorem matrixHeight_zero {n : Nat} :
    matrixHeight (0 : Matrix (Fin n) (Fin n) (Polynomial F)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [matrixHeight_le_iff]
  simp

theorem matrixHeight_add_le {n : Nat}
    (A B : Matrix (Fin n) (Fin n) (Polynomial F)) :
    matrixHeight (A + B) ≤ max (matrixHeight A) (matrixHeight B) := by
  rw [matrixHeight_le_iff]
  intro i j
  rw [Matrix.add_apply]
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le_max (natDegree_entry_le_matrixHeight A i j)
      (natDegree_entry_le_matrixHeight B i j))

theorem matrixHeight_mul_le {n : Nat}
    (A B : Matrix (Fin n) (Fin n) (Polynomial F)) :
    matrixHeight (A * B) ≤ matrixHeight A + matrixHeight B := by
  rw [matrixHeight_le_iff]
  intro i j
  rw [Matrix.mul_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (natDegree_entry_le_matrixHeight A i k)
      (natDegree_entry_le_matrixHeight B k j))

theorem matrixHeight_pow_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) (r : Nat) :
    matrixHeight (A ^ r) ≤ r * matrixHeight A := by
  induction r with
  | zero =>
      rw [Nat.zero_mul, matrixHeight_le_iff]
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> simp
  | succ r ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (matrixHeight_mul_le _ _).trans (Nat.add_le_add ih le_rfl)

theorem matrixHeight_smul_le {n : Nat} (a : Polynomial F)
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) :
    matrixHeight (a • A) ≤ a.natDegree + matrixHeight A := by
  rw [matrixHeight_le_iff]
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add le_rfl (natDegree_entry_le_matrixHeight A i j))

theorem vectorHeight_mulVec_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) (v : Fin n → Polynomial F) :
    vectorHeight (A *ᵥ v) ≤ matrixHeight A + vectorHeight v := by
  rw [vectorHeight_le_iff]
  intro i
  rw [Matrix.mulVec, dotProduct]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (natDegree_entry_le_matrixHeight A i j)
      (natDegree_vector_entry_le_vectorHeight v j))

/-- Evaluation of a polynomial at a square matrix over the coefficient ring. -/
def evalMatrix {n : Nat} (P : Polynomial (Polynomial F))
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) :
    Matrix (Fin n) (Fin n) (Polynomial F) :=
  P.sum fun r a => a • A ^ r

theorem matrixHeight_evalMatrix_le {n : Nat} (P : Polynomial (Polynomial F))
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) :
    matrixHeight (evalMatrix P A) ≤
      polyHeight P + P.natDegree * matrixHeight A := by
  rw [matrixHeight_le_iff]
  intro i j
  rw [evalMatrix, Polynomial.sum]
  rw [Matrix.sum_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  rw [Polynomial.mem_support_iff] at hr
  rw [Matrix.smul_apply, smul_eq_mul]
  refine Polynomial.natDegree_mul_le.trans ?_
  apply Nat.add_le_add
  · exact natDegree_coeff_le_height P r
  · exact (natDegree_entry_le_matrixHeight (A ^ r) i j).trans
      ((matrixHeight_pow_le A r).trans (Nat.mul_le_mul_right _
        (Polynomial.le_natDegree_of_ne_zero hr)))

theorem natDegree_det_le {n E : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (hM : ∀ i j, (M i j).natDegree ≤ E) :
    M.det.natDegree ≤ n * E := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  refine (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ)
    (∏ i : Fin n, M (σ i) i)).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ
    (fun i : Fin n => M (σ i) i)).trans ?_
  calc
    (∑ i : Fin n, (M (σ i) i).natDegree) ≤ ∑ _i : Fin n, E :=
      Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = n * E := by simp

theorem natDegree_det_le_matrixHeight {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F)) :
    M.det.natDegree ≤ n * matrixHeight M :=
  natDegree_det_le M (natDegree_entry_le_matrixHeight M)

theorem natDegree_adjugate_entry_le {n E : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (hM : ∀ i j, (M i j).natDegree ≤ E) (i j : Fin n) :
    (M.adjugate i j).natDegree ≤ n * E := by
  rw [Matrix.adjugate_apply]
  apply natDegree_det_le
  intro r c
  by_cases hr : r = j
  · subst r
    by_cases hc : c = i
    · subst c
      simp [Matrix.updateRow_apply]
    · simp [Matrix.updateRow_apply, hc]
  · simpa [Matrix.updateRow_apply, hr] using hM r c

/-- Cramer's-rule numerator identity, with no division and hence valid over `F[Z]`. -/
theorem adjugate_mulVec_mulVec {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (v : Fin n → Polynomial F) :
    M.adjugate *ᵥ (M *ᵥ v) = M.det • v := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem cramer_numerator_of_mulVec_eq {n E D : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (v b : Fin n → Polynomial F)
    (hM : ∀ i j, (M i j).natDegree ≤ E)
    (hb : ∀ i, (b i).natDegree ≤ D)
    (hsolve : M *ᵥ v = b) :
    M.det • v = M.adjugate *ᵥ b ∧
      ∀ i, ((M.adjugate *ᵥ b) i).natDegree ≤ n * E + D := by
  have hid := adjugate_mulVec_mulVec M v
  rw [hsolve] at hid
  refine ⟨hid.symm, ?_⟩
  have hadj : matrixHeight M.adjugate ≤ n * E := by
    rw [matrixHeight_le_iff]
    exact natDegree_adjugate_entry_le M hM
  have hbH : vectorHeight b ≤ D := by
    rw [vectorHeight_le_iff]
    exact hb
  intro i
  exact (natDegree_vector_entry_le_vectorHeight (M.adjugate *ᵥ b) i).trans
    ((vectorHeight_mulVec_le M.adjugate b).trans
      (Nat.add_le_add hadj hbH))

/-- The companion matrix for the relation
`T^h = -∑_{i<h} H_i T^i`.  The intended use has `H` monic of degree `h`;
the definition itself is total, including at `h = 0`. -/
def companionMatrix (h : Nat) (H : Polynomial (Polynomial F)) :
    Matrix (Fin h) (Fin h) (Polynomial F) := fun i j =>
  (if j.1 + 1 = i.1 then 1 else 0) -
    (if j.1 + 1 = h then H.coeff i.1 else 0)

theorem matrixHeight_companionMatrix_le (h : Nat)
    (H : Polynomial (Polynomial F)) :
    matrixHeight (companionMatrix h H) ≤ polyHeight H := by
  rw [matrixHeight_le_iff]
  intro i j
  unfold companionMatrix
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · split <;> simp
  · split
    · exact natDegree_coeff_le_height H i.1
    · simp

def lastIndex (h : Nat) (hh : 0 < h) : Fin h := ⟨h - 1, by omega⟩

def predIndex {h : Nat} (i : Fin h) (hi : 0 < i.1) : Fin h :=
  ⟨i.1 - 1, by omega⟩

theorem companionMatrix_mulVec_apply (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (v : Fin h → Polynomial F) (i : Fin h) :
    (companionMatrix h H *ᵥ v) i =
      (if hi : 0 < i.1 then v (predIndex i hi) else 0) -
        H.coeff i.1 * v (lastIndex h hh) := by
  classical
  unfold Matrix.mulVec dotProduct companionMatrix
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hlast (j : Fin h) : j.1 + 1 = h ↔ j = lastIndex h hh := by
    constructor
    · intro hj
      apply Fin.ext
      simp only [lastIndex]
      omega
    · rintro rfl
      simp only [lastIndex]
      omega
  have hlastSum :
      (∑ j : Fin h, (if j.1 + 1 = h then H.coeff i.1 else 0) * v j) =
        H.coeff i.1 * v (lastIndex h hh) := by
    simp_rw [hlast]
    simp
  rw [hlastSum]
  by_cases hi : 0 < i.1
  · simp only [dif_pos hi]
    have hpred (j : Fin h) : j.1 + 1 = i.1 ↔ j = predIndex i hi := by
      constructor
      · intro hj
        apply Fin.ext
        simp only [predIndex]
        omega
      · rintro rfl
        simp only [predIndex]
        omega
    simp_rw [hpred]
    simp
  · simp only [dif_neg hi]
    have hi0 : i.1 = 0 := by omega
    simp [hi0]

/-- Matrix of multiplication by `J`, expressed as `J` evaluated at the companion
matrix of `H`.  This construction never enters the fraction field. -/
def multiplicationMatrix (h : Nat) (H J : Polynomial (Polynomial F)) :
    Matrix (Fin h) (Fin h) (Polynomial F) :=
  evalMatrix J (companionMatrix h H)

/-- Polynomial represented by a coefficient vector in the basis
`1,T,...,T^(h-1)`. -/
def vectorPolynomial (h : Nat) (v : Fin h → Polynomial F) :
    Polynomial (Polynomial F) :=
  ∑ i : Fin h, Polynomial.monomial i.1 (v i)

@[simp] theorem coeff_vectorPolynomial (h : Nat) (v : Fin h → Polynomial F)
    (i : Fin h) : (vectorPolynomial h v).coeff i.1 = v i := by
  classical
  simp only [vectorPolynomial, Polynomial.finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    have hval : b.1 ≠ i.1 := fun h => hbi (Fin.ext h)
    simp [hval]
  · simp

theorem coeff_vectorPolynomial_eq_zero_of_le (h : Nat)
    (v : Fin h → Polynomial F) (i : Nat) (hi : h ≤ i) :
    (vectorPolynomial h v).coeff i = 0 := by
  classical
  simp only [vectorPolynomial, Polynomial.finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  split
  · rename_i heq
    have := j.2
    omega
  · rfl

theorem vectorPolynomial_degree_lt (h : Nat) (hh : 0 < h)
    (v : Fin h → Polynomial F) : (vectorPolynomial h v).degree < h := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  exact coeff_vectorPolynomial_eq_zero_of_le h v n hn

theorem vectorPolynomial_add (h : Nat)
    (v w : Fin h → Polynomial F) :
    vectorPolynomial h (v + w) = vectorPolynomial h v + vectorPolynomial h w := by
  classical
  apply Polynomial.ext
  intro n
  by_cases hn : n < h
  · let ni : Fin h := ⟨n, hn⟩
    rw [coeff_vectorPolynomial h (v + w) ni,
      coeff_add, coeff_vectorPolynomial h v ni, coeff_vectorPolynomial h w ni]
    rfl
  · have hle : h ≤ n := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h (v + w) n hle,
      coeff_add, coeff_vectorPolynomial_eq_zero_of_le h v n hle,
      coeff_vectorPolynomial_eq_zero_of_le h w n hle, add_zero]

theorem vectorPolynomial_smul (h : Nat) (a : Polynomial F)
    (v : Fin h → Polynomial F) :
    vectorPolynomial h (a • v) = Polynomial.C a * vectorPolynomial h v := by
  classical
  apply Polynomial.ext
  intro n
  by_cases hn : n < h
  · let ni : Fin h := ⟨n, hn⟩
    rw [coeff_vectorPolynomial h (a • v) ni, coeff_C_mul,
      coeff_vectorPolynomial h v ni]
    rfl
  · have hle : h ≤ n := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h (a • v) n hle,
      coeff_C_mul, coeff_vectorPolynomial_eq_zero_of_le h v n hle, mul_zero]

@[simp] theorem evalMatrix_add {n : Nat} (P Q : Polynomial (Polynomial F))
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) :
    evalMatrix (P + Q) A = evalMatrix P A + evalMatrix Q A := by
  unfold evalMatrix
  apply Polynomial.sum_add_index <;> simp [add_smul]

@[simp] theorem evalMatrix_monomial {n : Nat} (r : Nat) (a : Polynomial F)
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) :
    evalMatrix (Polynomial.monomial r a) A = a • A ^ r := by
  unfold evalMatrix
  rw [Polynomial.sum_monomial_index]
  simp

theorem companionPolynomial_identity (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (v : Fin h → Polynomial F) :
    Polynomial.X * vectorPolynomial h v =
      vectorPolynomial h (companionMatrix h H *ᵥ v) +
        Polynomial.C (v (lastIndex h hh)) * H := by
  classical
  apply Polynomial.ext
  intro n
  by_cases hnlt : n < h
  · let ni : Fin h := ⟨n, hnlt⟩
    by_cases hn0 : n = 0
    · subst n
      rw [Polynomial.coeff_X_mul_zero]
      simp only [coeff_add, coeff_C_mul]
      have hcv := companionMatrix_mulVec_apply h hh H v ni
      simp only [ni, Fin.val_zero, lt_self_iff_false, dite_false] at hcv
      rw [coeff_vectorPolynomial h (companionMatrix h H *ᵥ v) ni, hcv]
      ring
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [Polynomial.coeff_X_mul]
      simp only [coeff_add, coeff_C_mul]
      have hm : m < h := by omega
      let mi : Fin h := ⟨m, hm⟩
      rw [coeff_vectorPolynomial h v mi]
      have hcv := companionMatrix_mulVec_apply h hh H v ni
      have hpos : 0 < ni.1 := by simp [ni]
      simp only [dif_pos hpos] at hcv
      rw [coeff_vectorPolynomial h (companionMatrix h H *ᵥ v) ni, hcv]
      have hpred : predIndex ni hpos = mi := by
        apply Fin.ext
        simp [predIndex, ni, mi]
      rw [hpred]
      ring
  · have hle : h ≤ n := by omega
    by_cases hnh : n = h
    · subst n
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
      have hlhs : (Polynomial.X * vectorPolynomial h v).coeff h =
          (vectorPolynomial h v).coeff m := by
        exact (congrArg (fun r =>
          (Polynomial.X * vectorPolynomial h v).coeff r) hm).trans
            (Polynomial.coeff_X_mul (vectorPolynomial h v) m)
      rw [hlhs]
      simp only [coeff_add, coeff_C_mul]
      rw [coeff_vectorPolynomial_eq_zero_of_le h
        (companionMatrix h H *ᵥ v) h le_rfl]
      have hmlt : m < h := by omega
      let mi : Fin h := ⟨m, hmlt⟩
      rw [coeff_vectorPolynomial h v mi]
      have hlast : lastIndex h hh = mi := by
        apply Fin.ext
        simp [lastIndex, mi]
        omega
      have htop : H.coeff h = 1 := by
        rw [← hHdeg]
        exact hH.coeff_natDegree
      rw [hlast, htop]
      simp
    · have hgt : h < n := by omega
      have hnpos : 0 < n := hh.trans hgt
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      rw [Polynomial.coeff_X_mul]
      simp only [coeff_add, coeff_C_mul]
      rw [coeff_vectorPolynomial_eq_zero_of_le h v m (by omega)]
      rw [coeff_vectorPolynomial_eq_zero_of_le h
        (companionMatrix h H *ᵥ v) (m + 1) (by omega)]
      have hHcoeff : H.coeff (m + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hHdeg]
        omega
      rw [hHcoeff]
      simp

theorem companionMatrix_represents_mulX_mod (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (v : Fin h → Polynomial F) :
    canonicalRemainder H (Polynomial.X * vectorPolynomial h v) =
      vectorPolynomial h (companionMatrix h H *ᵥ v) := by
  have hid := companionPolynomial_identity h hh H hH hHdeg v
  have hdvd : H ∣ Polynomial.X * vectorPolynomial h v -
      vectorPolynomial h (companionMatrix h H *ᵥ v) := by
    refine ⟨Polynomial.C (v (lastIndex h hh)), ?_⟩
    rw [hid]
    ring
  calc
    canonicalRemainder H (Polynomial.X * vectorPolynomial h v) =
        canonicalRemainder H
          (vectorPolynomial h (companionMatrix h H *ᵥ v)) := by
      exact Polynomial.modByMonic_eq_of_dvd_sub hH hdvd
    _ = vectorPolynomial h (companionMatrix h H *ᵥ v) :=
      canonicalRemainder_eq_self hH (by
        rw [H.degree_eq_natDegree hH.ne_zero, hHdeg]
        exact vectorPolynomial_degree_lt h hh (companionMatrix h H *ᵥ v))

theorem companionMatrix_pow_divisibility (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (v : Fin h → Polynomial F) (r : Nat) :
    H ∣ Polynomial.X ^ r * vectorPolynomial h v -
      vectorPolynomial h ((companionMatrix h H) ^ r *ᵥ v) := by
  induction r with
  | zero => simp
  | succ r ih =>
      let C := companionMatrix h H
      let w : Fin h → Polynomial F := C ^ r *ᵥ v
      have hstepId := companionPolynomial_identity h hh H hH hHdeg w
      have hstep : H ∣ Polynomial.X * vectorPolynomial h w -
          vectorPolynomial h (C *ᵥ w) := by
        refine ⟨Polynomial.C (w (lastIndex h hh)), ?_⟩
        rw [hstepId]
        ring
      obtain ⟨q, hq⟩ := ih
      obtain ⟨s, hs⟩ := hstep
      refine ⟨Polynomial.X * q + s, ?_⟩
      have haction : C *ᵥ w = C ^ (r + 1) *ᵥ v := by
        simp only [w, Matrix.mulVec_mulVec]
        rw [← pow_succ']
      rw [pow_succ' (Polynomial.X : Polynomial (Polynomial F))]
      rw [← haction]
      dsimp only [w] at hs
      change Polynomial.X ^ r * vectorPolynomial h v -
        vectorPolynomial h (C ^ r *ᵥ v) = H * q at hq
      dsimp only [w]
      calc
        Polynomial.X * Polynomial.X ^ r * vectorPolynomial h v -
            vectorPolynomial h (C *ᵥ C ^ r *ᵥ v) =
          Polynomial.X * (Polynomial.X ^ r * vectorPolynomial h v -
              vectorPolynomial h (C ^ r *ᵥ v)) +
            (Polynomial.X * vectorPolynomial h (C ^ r *ᵥ v) -
              vectorPolynomial h (C *ᵥ C ^ r *ᵥ v)) := by ring
        _ = Polynomial.X * (H * q) + H * s := by rw [hq, hs]
        _ = H * (Polynomial.X * q + s) := by ring

theorem companionMatrix_pow_represents_mul_mod (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (v : Fin h → Polynomial F) (r : Nat) :
    canonicalRemainder H (Polynomial.X ^ r * vectorPolynomial h v) =
      vectorPolynomial h ((companionMatrix h H) ^ r *ᵥ v) := by
  calc
    canonicalRemainder H (Polynomial.X ^ r * vectorPolynomial h v) =
        canonicalRemainder H
          (vectorPolynomial h ((companionMatrix h H) ^ r *ᵥ v)) := by
      exact Polynomial.modByMonic_eq_of_dvd_sub hH
        (companionMatrix_pow_divisibility h hh H hH hHdeg v r)
    _ = vectorPolynomial h ((companionMatrix h H) ^ r *ᵥ v) :=
      canonicalRemainder_eq_self hH (by
        rw [H.degree_eq_natDegree hH.ne_zero, hHdeg]
        exact vectorPolynomial_degree_lt h hh ((companionMatrix h H) ^ r *ᵥ v))

theorem multiplicationMatrix_divisibility (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (v : Fin h → Polynomial F) (J : Polynomial (Polynomial F)) :
    H ∣ J * vectorPolynomial h v -
      vectorPolynomial h (multiplicationMatrix h H J *ᵥ v) := by
  induction J using Polynomial.induction_on' with
  | add P Q hP hQ =>
      obtain ⟨p, hp⟩ := hP
      obtain ⟨q, hq⟩ := hQ
      refine ⟨p + q, ?_⟩
      simp only [multiplicationMatrix]
      rw [evalMatrix_add, Matrix.add_mulVec, vectorPolynomial_add]
      change P * vectorPolynomial h v -
        vectorPolynomial h (evalMatrix P (companionMatrix h H) *ᵥ v) = H * p at hp
      change Q * vectorPolynomial h v -
        vectorPolynomial h (evalMatrix Q (companionMatrix h H) *ᵥ v) = H * q at hq
      calc
        (P + Q) * vectorPolynomial h v -
            (vectorPolynomial h (evalMatrix P (companionMatrix h H) *ᵥ v) +
              vectorPolynomial h (evalMatrix Q (companionMatrix h H) *ᵥ v)) =
          (P * vectorPolynomial h v -
              vectorPolynomial h (evalMatrix P (companionMatrix h H) *ᵥ v)) +
            (Q * vectorPolynomial h v -
              vectorPolynomial h (evalMatrix Q (companionMatrix h H) *ᵥ v)) := by ring
        _ = H * p + H * q := by rw [hp, hq]
        _ = H * (p + q) := by ring
  | monomial r a =>
      obtain ⟨q, hq⟩ :=
        companionMatrix_pow_divisibility h hh H hH hHdeg v r
      refine ⟨Polynomial.C a * q, ?_⟩
      simp only [multiplicationMatrix, evalMatrix_monomial,
        Matrix.smul_mulVec, vectorPolynomial_smul]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      calc
        Polynomial.C a * Polynomial.X ^ r * vectorPolynomial h v -
            Polynomial.C a *
              vectorPolynomial h (companionMatrix h H ^ r *ᵥ v) =
          Polynomial.C a * (Polynomial.X ^ r * vectorPolynomial h v -
            vectorPolynomial h (companionMatrix h H ^ r *ᵥ v)) := by ring
        _ = Polynomial.C a * (H * q) := by rw [hq]
        _ = H * (Polynomial.C a * q) := by ring

theorem multiplicationMatrix_represents_mul_mod (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (J : Polynomial (Polynomial F)) (v : Fin h → Polynomial F) :
    canonicalRemainder H (J * vectorPolynomial h v) =
      vectorPolynomial h (multiplicationMatrix h H J *ᵥ v) := by
  calc
    canonicalRemainder H (J * vectorPolynomial h v) =
        canonicalRemainder H
          (vectorPolynomial h (multiplicationMatrix h H J *ᵥ v)) := by
      exact Polynomial.modByMonic_eq_of_dvd_sub hH
        (multiplicationMatrix_divisibility h hh H hH hHdeg v J)
    _ = vectorPolynomial h (multiplicationMatrix h H J *ᵥ v) :=
      canonicalRemainder_eq_self hH (by
        rw [H.degree_eq_natDegree hH.ne_zero, hHdeg]
        exact vectorPolynomial_degree_lt h hh (multiplicationMatrix h H J *ᵥ v))

theorem mulVec_adjugate_mulVec {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (b : Fin n → Polynomial F) :
    M *ᵥ (M.adjugate *ᵥ b) = M.det • b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Integral Bézout/Cramer identity in `(F[Z])[T]/(H)`.  Multiplication by `J`
on the adjugate numerator is multiplication by the scalar determinant `q`.
This is the division-free statement behind every finite Taylor step. -/
theorem multiplicationMatrix_adjugate_bezout (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (J : Polynomial (Polynomial F)) (b : Fin h → Polynomial F) :
    let M := multiplicationMatrix h H J
    let q := M.det
    canonicalRemainder H (J * vectorPolynomial h (M.adjugate *ᵥ b)) =
      Polynomial.C q * vectorPolynomial h b := by
  dsimp only
  rw [multiplicationMatrix_represents_mul_mod h hh H hH hHdeg]
  rw [mulVec_adjugate_mulVec]
  exact vectorPolynomial_smul h _ b

theorem matrixHeight_multiplicationMatrix_le (h : Nat)
    (H J : Polynomial (Polynomial F)) :
    matrixHeight (multiplicationMatrix h H J) ≤
      polyHeight J + J.natDegree * polyHeight H := by
  exact (matrixHeight_evalMatrix_le J (companionMatrix h H)).trans
    (Nat.add_le_add_left
      (Nat.mul_le_mul_left J.natDegree (matrixHeight_companionMatrix_le h H)) _)

theorem natDegree_det_multiplicationMatrix_le (h : Nat)
    (H J : Polynomial (Polynomial F)) :
    (multiplicationMatrix h H J).det.natDegree ≤
      h * (polyHeight J + J.natDegree * polyHeight H) := by
  exact (natDegree_det_le_matrixHeight (multiplicationMatrix h H J)).trans
    (Nat.mul_le_mul_left h (matrixHeight_multiplicationMatrix_le h H J))

theorem natDegree_adjugate_multiplicationMatrix_entry_le (h : Nat)
    (H J : Polynomial (Polynomial F)) (i j : Fin h) :
    ((multiplicationMatrix h H J).adjugate i j).natDegree ≤
      h * (polyHeight J + J.natDegree * polyHeight H) := by
  apply natDegree_adjugate_entry_le
  intro r c
  exact (natDegree_entry_le_matrixHeight (multiplicationMatrix h H J) r c).trans
    (matrixHeight_multiplicationMatrix_le h H J)

/-- The determinant/adjugate numerator certificate used at every Taylor step. -/
theorem multiplicationMatrix_numerator_certificate (h : Nat)
    (H J : Polynomial (Polynomial F)) (v : Fin h → Polynomial F) :
    let M := multiplicationMatrix h H J
    M.adjugate *ᵥ (M *ᵥ v) = M.det • v ∧
      M.det.natDegree ≤ h * (polyHeight J + J.natDegree * polyHeight H) ∧
      ∀ i j, (M.adjugate i j).natDegree ≤
        h * (polyHeight J + J.natDegree * polyHeight H) := by
  dsimp only
  exact ⟨adjugate_mulVec_mulVec _ _, natDegree_det_multiplicationMatrix_le h H J,
    natDegree_adjugate_multiplicationMatrix_entry_le h H J⟩

/-- Exponent of the common denominator of the `t`-th finite Taylor coefficient.
It is `0,1,3,5,...`, i.e. `2t-1` for positive `t`. -/
def oddDenomExponent : Nat → Nat
  | 0 => 0
  | t + 1 => 2 * t + 1

theorem oddDenomExponent_eq (t : Nat) (ht : 0 < t) :
    oddDenomExponent t = 2 * t - 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp [oddDenomExponent]
  omega

def finiteTaylorDenominator (q : Polynomial F) (t : Nat) : Polynomial F :=
  q ^ oddDenomExponent t

@[simp] theorem finiteTaylorDenominator_zero (q : Polynomial F) :
    finiteTaylorDenominator q 0 = 1 := by
  simp [finiteTaylorDenominator, oddDenomExponent]

@[simp] theorem finiteTaylorDenominator_one (q : Polynomial F) :
    finiteTaylorDenominator q 1 = q := by
  simp [finiteTaylorDenominator, oddDenomExponent]

theorem finiteTaylorDenominator_succ_succ (q : Polynomial F) (t : Nat) :
    finiteTaylorDenominator q (t + 2) =
      q ^ 2 * finiteTaylorDenominator q (t + 1) := by
  simp only [finiteTaylorDenominator, oddDenomExponent]
  rw [← pow_add]
  congr 1
  omega

end MatrixHeight

end

end ProximityPrize.SubmissionLower.FiniteTaylorCore
