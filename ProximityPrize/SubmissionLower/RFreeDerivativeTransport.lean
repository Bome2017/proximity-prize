import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C1
import ProximityPrize.SubmissionLower.C6
import ProximityPrize.SubmissionLower.K
import ProximityPrize.SubmissionLower.W2
namespace ProximityPrize.SubmissionLower.RFreeDerivativeTransport
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research ContactFlagInterpolation6641Research
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

variable (K : Type*) [Field K]

abbrev LocalCoefficient := MvPolynomial (Fin 3) K
abbrev LocalPolynomial := Polynomial (LocalCoefficient K)

def localA : LocalCoefficient K := MvPolynomial.X 0
def localB : LocalCoefficient K := MvPolynomial.X 1
def localZ : LocalCoefficient K := MvPolynomial.X 2
def localDelta : LocalCoefficient K := localA K - localB K

def localVariables (x u0 u1 : K) : Fin 4 → LocalPolynomial K :=
  ![Polynomial.X + Polynomial.C (MvPolynomial.C x),
    Polynomial.C (MvPolynomial.C u0) +
      Polynomial.C (MvPolynomial.C u1) * Polynomial.C (localZ K) +
      Polynomial.X * Polynomial.C (localA K),
    Polynomial.C (localB K),
    Polynomial.C (localZ K)]

def localTranslation (x u0 u1 : K) :
    MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K :=
  MvPolynomial.aeval (localVariables K x u0 u1)

def HasContact (m : ℕ) (P : LocalPolynomial K) : Prop :=
  ∀ r : ℕ, localDelta K ^ (m - r) ∣ P.coeff r

abbrev ScaledCoefficient := MvPolynomial (Fin 4) K
abbrev ScaledPolynomial := Polynomial (ScaledCoefficient K)

def scaledB : ScaledCoefficient K := MvPolynomial.X 0
def scaledD : ScaledCoefficient K := MvPolynomial.X 1
def scaledU : ScaledCoefficient K := MvPolynomial.X 2
def scaledZ : ScaledCoefficient K := MvPolynomial.X 3

def coefficientScaling :
    LocalCoefficient K →ₐ[K] ScaledPolynomial K :=
  MvPolynomial.aeval
    ![Polynomial.C (scaledB K) + Polynomial.X * Polynomial.C (scaledD K),
      Polynomial.C (scaledB K), Polynomial.C (scaledZ K)]

def contactScaling : LocalPolynomial K →ₐ[K] ScaledPolynomial K :=
  Polynomial.eval₂AlgHom (coefficientScaling K)
    (Polynomial.X * Polynomial.C (scaledU K))
      (fun a ↦ Commute.all (coefficientScaling K a)
        (Polynomial.X * Polynomial.C (scaledU K)))

@[simp] theorem coefficientScaling_localDelta :
    coefficientScaling K (localDelta K) =
      Polynomial.X * Polynomial.C (scaledD K) := by
  simp [coefficientScaling, localDelta, localA, localB]

@[simp] theorem contactScaling_X :
    contactScaling K (Polynomial.X : LocalPolynomial K) =
      Polynomial.X * Polynomial.C (scaledU K) := by
  simp [contactScaling]

@[simp] theorem contactScaling_C (a : LocalCoefficient K) :
    contactScaling K (Polynomial.C a) = coefficientScaling K a := by
  simp [contactScaling]

theorem factor_trailingDegree_lower_bound
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    (P Q : Polynomial A) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (m h : ℕ) (hproduct : m ≤ (P * Q).natTrailingDegree)
    (hQorder : Q.natTrailingDegree = h) :
    m - h ≤ P.natTrailingDegree := by
  rw [Polynomial.natTrailingDegree_mul hP hQ, hQorder] at hproduct
  omega

theorem coefficientScaling_dvd_of_delta_pow_dvd
    (a : LocalCoefficient K) (k : ℕ)
    (h : localDelta K ^ k ∣ a) :
    (Polynomial.X : ScaledPolynomial K) ^ k ∣ coefficientScaling K a := by
  have hmapped := map_dvd (coefficientScaling K) h
  rw [map_pow, coefficientScaling_localDelta] at hmapped
  have hfactor :
      (Polynomial.X : ScaledPolynomial K) ^ k ∣
        (Polynomial.X * Polynomial.C (scaledD K)) ^ k :=
    pow_dvd_pow_of_dvd (dvd_mul_right Polynomial.X _) k
  exact hfactor.trans hmapped

theorem contactScaling_term_dvd
    (a : LocalCoefficient K) (m r : ℕ)
    (h : localDelta K ^ (m - r) ∣ a) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣
      contactScaling K
        (Polynomial.C a * (Polynomial.X : LocalPolynomial K) ^ r) := by
  rw [map_mul, map_pow, contactScaling_C, contactScaling_X]
  have ha := coefficientScaling_dvd_of_delta_pow_dvd K a (m - r) h
  have hx :
      (Polynomial.X : ScaledPolynomial K) ^ r ∣
        (Polynomial.X * Polynomial.C (scaledU K)) ^ r :=
    pow_dvd_pow_of_dvd (dvd_mul_right Polynomial.X _) r
  have hproduct := mul_dvd_mul ha hx
  have htotal :
      (Polynomial.X : ScaledPolynomial K) ^ ((m - r) + r) ∣
        coefficientScaling K a *
          (Polynomial.X * Polynomial.C (scaledU K)) ^ r := by
    simpa only [pow_add] using hproduct
  exact (pow_dvd_pow Polynomial.X (by omega : m ≤ (m - r) + r)).trans htotal

theorem HasContact.contactScaling_dvd
    (P : LocalPolynomial K) (m : ℕ) (hP : HasContact K m P) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣ contactScaling K P := by
  rw [P.as_sum_support_C_mul_X_pow, map_sum]
  apply Finset.dvd_sum
  intro r hr
  exact contactScaling_term_dvd K (P.coeff r) m r (hP r)

def scaledCoefficientDerivation (i : Fin 4) :
    Derivation K (ScaledPolynomial K) (ScaledPolynomial K) :=
  PolynomialModule.equivPolynomialSelf.compDer
    ((MvPolynomial.pderiv i :
      Derivation K (ScaledCoefficient K) (ScaledCoefficient K)).mapCoeffs)

@[simp] theorem scaledCoefficientDerivation_coeff
    (i : Fin 4) (P : ScaledPolynomial K) (n : ℕ) :
    (scaledCoefficientDerivation K i P).coeff n =
      MvPolynomial.pderiv i (P.coeff n) := rfl

@[simp] theorem scaledCoefficientDerivation_X (i : Fin 4) :
    scaledCoefficientDerivation K i
      (Polynomial.X : ScaledPolynomial K) = 0 := by
  ext n
  rw [scaledCoefficientDerivation_coeff]
  by_cases hn : n = 1
  · subst n
    simp
  · simp [Polynomial.coeff_X, Ne.symm hn]

@[simp] theorem scaledCoefficientDerivation_C
    (i : Fin 4) (a : ScaledCoefficient K) :
    scaledCoefficientDerivation K i (Polynomial.C a) =
      Polynomial.C (MvPolynomial.pderiv i a) := by
  ext n
  rw [scaledCoefficientDerivation_coeff]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [Polynomial.coeff_C, hn]

def scaledContactDerivation :
    Derivation K (ScaledPolynomial K) (ScaledPolynomial K) :=
  (Polynomial.X : ScaledPolynomial K) • scaledCoefficientDerivation K 0 -
    scaledCoefficientDerivation K 1

theorem scaledContactDerivation_apply (P : ScaledPolynomial K) :
    scaledContactDerivation K P =
      Polynomial.X * scaledCoefficientDerivation K 0 P -
        scaledCoefficientDerivation K 1 P := by
  simp [scaledContactDerivation, smul_eq_mul]

def scaledLocalVariables (x u0 u1 : K) : Fin 4 → ScaledPolynomial K :=
  ![Polynomial.C (MvPolynomial.C x) +
      Polynomial.X * Polynomial.C (scaledU K),
    Polynomial.C (MvPolynomial.C u0) +
      Polynomial.C (MvPolynomial.C u1) * Polynomial.C (scaledZ K) +
      (Polynomial.X * Polynomial.C (scaledU K)) *
        (Polynomial.C (scaledB K) +
          Polynomial.X * Polynomial.C (scaledD K)),
    Polynomial.C (scaledB K), Polynomial.C (scaledZ K)]

def scaledLocalTranslation (x u0 u1 : K) :
    MvPolynomial (Fin 4) K →ₐ[K] ScaledPolynomial K :=
  MvPolynomial.aeval (scaledLocalVariables K x u0 u1)

@[simp] theorem scaledContactDerivation_localVariable
    (x u0 u1 : K) (i : Fin 4) :
    scaledContactDerivation K (scaledLocalVariables K x u0 u1 i) =
      if i = 2 then Polynomial.X else 0 := by
  rw [scaledContactDerivation_apply]
  fin_cases i <;>
    simp [scaledLocalVariables, scaledB, scaledD, scaledU, scaledZ,
      MvPolynomial.pderiv_X] <;> ring

theorem scaledLocalTranslation_eq_contactScaling
    (x u0 u1 : K) (Q : MvPolynomial (Fin 4) K) :
    scaledLocalTranslation K x u0 u1 Q =
      contactScaling K (localTranslation K x u0 u1 Q) := by
  have hhom : scaledLocalTranslation K x u0 u1 =
      (contactScaling K).comp (localTranslation K x u0 u1) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [scaledLocalTranslation, scaledLocalVariables, localTranslation,
        localVariables, contactScaling, coefficientScaling, localA, localB,
        localZ, scaledB, scaledD, scaledU, scaledZ] <;> ring
  exact DFunLike.congr_fun hhom Q

theorem scaledContactDerivation_localTranslation
    (x u0 u1 : K) (Q : MvPolynomial (Fin 4) K) :
    scaledContactDerivation K (scaledLocalTranslation K x u0 u1 Q) =
      Polynomial.X *
        scaledLocalTranslation K x u0 u1
          (MvPolynomial.pderiv (2 : Fin 4) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      rw [scaledContactDerivation_apply]
      simp [scaledLocalTranslation]
  | add P Q hP hQ => simp only [map_add, hP, hQ, mul_add]
  | mul_X P i hP =>
      rw [map_mul, Derivation.leibniz, hP]
      have hvar :
          scaledContactDerivation K
              (scaledLocalTranslation K x u0 u1 (MvPolynomial.X i)) =
            if i = 2 then Polynomial.X else 0 := by
        rw [show scaledLocalTranslation K x u0 u1 (MvPolynomial.X i) =
          scaledLocalVariables K x u0 u1 i by
            simp only [scaledLocalTranslation, MvPolynomial.aeval_X]]
        exact scaledContactDerivation_localVariable K x u0 u1 i
      rw [hvar, MvPolynomial.pderiv_mul, map_add, map_mul]
      by_cases hi : i = 2
      · subst i
        simp [scaledLocalTranslation, scaledLocalVariables, smul_eq_mul]
        ring
      · simp [hi, scaledLocalTranslation, smul_eq_mul]
        ring

theorem X_pow_dvd_scaledCoefficientDerivation
    (i : Fin 4) (P : ScaledPolynomial K) (m : ℕ)
    (hP : (Polynomial.X : ScaledPolynomial K) ^ m ∣ P) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledCoefficientDerivation K i P := by
  rw [Polynomial.X_pow_dvd_iff] at hP ⊢
  intro n hn
  rw [scaledCoefficientDerivation_coeff, hP n hn, map_zero]

theorem X_pow_dvd_scaledContactDerivation
    (P : ScaledPolynomial K) (m : ℕ)
    (hP : (Polynomial.X : ScaledPolynomial K) ^ m ∣ P) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledContactDerivation K P := by
  rw [scaledContactDerivation_apply]
  apply dvd_sub
  · exact dvd_mul_of_dvd_right
      (X_pow_dvd_scaledCoefficientDerivation K 0 P m hP) Polynomial.X
  · exact X_pow_dvd_scaledCoefficientDerivation K 1 P m hP

theorem X_pow_pred_dvd_of_X_mul_dvd
    (P : ScaledPolynomial K) (m : ℕ)
    (hP : (Polynomial.X : ScaledPolynomial K) ^ m ∣ Polynomial.X * P) :
    (Polynomial.X : ScaledPolynomial K) ^ (m - 1) ∣ P := by
  rw [Polynomial.X_pow_dvd_iff] at hP ⊢
  intro n hn
  have hnext := hP (n + 1) (by omega)
  simpa [Polynomial.coeff_X_mul] using hnext

theorem scaledLocalTranslation_pderiv_R_order_loss
    (x u0 u1 : K) (Q : MvPolynomial (Fin 4) K) (m : ℕ)
    (hQ : (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledLocalTranslation K x u0 u1 Q) :
    (Polynomial.X : ScaledPolynomial K) ^ (m - 1) ∣
      scaledLocalTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4) Q) := by
  have hder := X_pow_dvd_scaledContactDerivation K
    (scaledLocalTranslation K x u0 u1 Q) m hQ
  rw [scaledContactDerivation_localTranslation] at hder
  exact X_pow_pred_dvd_of_X_mul_dvd K _ m hder

theorem X_pow_dvd_of_le_natTrailingDegree
    (P : ScaledPolynomial K) (m : ℕ)
    (horder : m ≤ P.natTrailingDegree) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣ P := by
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    (hn.trans_le horder)

theorem pderiv_R_factor_scaled_order
    (x u0 u1 : K) (G H : MvPolynomial (Fin 4) K) (m h : ℕ)
    (hproduct : (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledLocalTranslation K x u0 u1 (G * H))
    (hH : scaledLocalTranslation K x u0 u1 H ≠ 0)
    (hHorder :
      (scaledLocalTranslation K x u0 u1 H).natTrailingDegree = h) :
    (Polynomial.X : ScaledPolynomial K) ^ ((m - h) - 1) ∣
      scaledLocalTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4) G) := by
  by_cases hG : scaledLocalTranslation K x u0 u1 G = 0
  · have hcomm := scaledContactDerivation_localTranslation K x u0 u1 G
    rw [hG, map_zero] at hcomm
    have hzero : scaledLocalTranslation K x u0 u1
        (MvPolynomial.pderiv (2 : Fin 4) G) = 0 := by
      exact (mul_eq_zero.mp hcomm.symm).resolve_left Polynomial.X_ne_zero
    rw [hzero]
    exact dvd_zero _
  have hmul : scaledLocalTranslation K x u0 u1 (G * H) =
      scaledLocalTranslation K x u0 u1 G *
        scaledLocalTranslation K x u0 u1 H := map_mul _ _ _
  have hproduct_ne : scaledLocalTranslation K x u0 u1 (G * H) ≠ 0 := by
    rw [hmul]
    exact mul_ne_zero hG hH
  have hproduct_order :
      m ≤ (scaledLocalTranslation K x u0 u1 (G * H)).natTrailingDegree := by
    apply Polynomial.le_natTrailingDegree hproduct_ne
    exact Polynomial.X_pow_dvd_iff.mp hproduct
  rw [hmul] at hproduct_order
  have hGorder : m - h ≤
      (scaledLocalTranslation K x u0 u1 G).natTrailingDegree :=
    factor_trailingDegree_lower_bound
      (scaledLocalTranslation K x u0 u1 G)
      (scaledLocalTranslation K x u0 u1 H)
      hG hH m h hproduct_order hHorder
  have hGcontact := X_pow_dvd_of_le_natTrailingDegree K
    (scaledLocalTranslation K x u0 u1 G) (m - h) hGorder
  exact scaledLocalTranslation_pderiv_R_order_loss K x u0 u1 G (m - h) hGcontact

def scaledCoefficientEvaluation
    (R D : Polynomial K) (gamma : K) :
    ScaledCoefficient K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![R, D, 1, Polynomial.C gamma]

def scaledEvaluation (R D : Polynomial K) (gamma : K) :
    ScaledPolynomial K →ₐ[K] Polynomial K :=
  Polynomial.eval₂AlgHom (scaledCoefficientEvaluation K R D gamma)
    Polynomial.X
      (fun a ↦ Commute.all (scaledCoefficientEvaluation K R D gamma a)
        Polynomial.X)

def globalSpecialization (P : Polynomial K) (gamma : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval
    ![Polynomial.X, P, P.derivative, Polynomial.C gamma]

@[simp] theorem scaledEvaluation_X
    (R D : Polynomial K) (gamma : K) :
    scaledEvaluation K R D gamma
      (Polynomial.X : ScaledPolynomial K) = Polynomial.X := by
  simp [scaledEvaluation]

theorem scaledEvaluation_localTranslation
    (Q : MvPolynomial (Fin 4) K) (P R D : Polynomial K)
    (x u0 u1 gamma : K)
    (hR : R = Polynomial.taylor x P.derivative)
    (hP : Polynomial.taylor x P =
      Polynomial.C (u0 + gamma * u1) +
        Polynomial.X * (R + Polynomial.X * D)) :
    scaledEvaluation K R D gamma
        (scaledLocalTranslation K x u0 u1 Q) =
      Polynomial.taylor x (globalSpecialization K P gamma Q) := by
  have hhom :
      (scaledEvaluation K R D gamma).comp
          (scaledLocalTranslation K x u0 u1) =
        (Polynomial.taylorAlgHom x).comp
          (globalSpecialization K P gamma) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [scaledEvaluation, scaledCoefficientEvaluation,
        scaledLocalTranslation, scaledLocalVariables, globalSpecialization,
        scaledB, scaledD, scaledU, scaledZ, hR, hP] <;> ring
  exact DFunLike.congr_fun hhom Q

theorem X_pow_dvd_taylor_globalSpecialization_of_scaled
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K)
    (x u0 u1 gamma : K) (m : ℕ)
    (hvalue : P.eval x = u0 + gamma * u1)
    (hcontact : (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledLocalTranslation K x u0 u1 Q) :
    (Polynomial.X : Polynomial K) ^ m ∣
      Polynomial.taylor x (globalSpecialization K P gamma Q) := by
  obtain ⟨D, hD⟩ :=
    ContactLocalDivisibility.X_sq_dvd_contactResidual P x
  let R := Polynomial.taylor x P.derivative
  have hP : Polynomial.taylor x P =
      Polynomial.C (u0 + gamma * u1) +
        Polynomial.X * (R + Polynomial.X * D) := by
    change Polynomial.taylor x P - Polynomial.C (P.eval x) -
      Polynomial.X * Polynomial.taylor x P.derivative =
        Polynomial.X ^ 2 * D at hD
    rw [hvalue] at hD
    dsimp only [R]
    linear_combination hD
  have hmapped := map_dvd (scaledEvaluation K R D gamma) hcontact
  rw [map_pow, scaledEvaluation_X,
    scaledEvaluation_localTranslation K Q P R D x u0 u1 gamma rfl hP]
    at hmapped
  exact hmapped

theorem rootMultiplicity_ge_of_taylor_dvd
    (F : Polynomial K) (x : K) (m : ℕ) (hF : F ≠ 0)
    (hdiv : (Polynomial.X : Polynomial K) ^ m ∣ Polynomial.taylor x F) :
    m ≤ F.rootMultiplicity x := by
  apply (Polynomial.le_rootMultiplicity_iff hF).mpr
  have hshift : Polynomial.taylor x
      ((Polynomial.X - Polynomial.C x) ^ m) =
      (Polynomial.X : Polynomial K) ^ m := by
    rw [Polynomial.taylor_pow, map_sub, Polynomial.taylor_X,
      Polynomial.taylor_C, add_sub_cancel_right]
  have hequiv := map_dvd_iff (Polynomial.taylorEquiv x)
    (a := (Polynomial.X - Polynomial.C x) ^ m) (b := F)
  change Polynomial.taylor x ((Polynomial.X - Polynomial.C x) ^ m) ∣
      Polynomial.taylor x F ↔
    (Polynomial.X - Polynomial.C x) ^ m ∣ F at hequiv
  exact hequiv.mp (by simpa only [hshift] using hdiv)

theorem eq_zero_of_rootMultiplicity_sum
    {I : Type*} [Fintype I] (F : Polynomial K) (nodes : I ↪ K)
    (support : Finset I) (multiplicity : I → ℕ)
    (hmult : ∀ i ∈ support,
      multiplicity i ≤ F.rootMultiplicity (nodes i))
    (hdegree : F.natDegree < ∑ i ∈ support, multiplicity i) :
    F = 0 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  by_contra hF
  let points : Finset K := support.map nodes
  have hselected :
      (∑ i ∈ support, multiplicity i) ≤
        ∑ x ∈ points, F.rootMultiplicity x := by
    calc
      (∑ i ∈ support, multiplicity i) ≤
          ∑ i ∈ support, F.rootMultiplicity (nodes i) :=
        Finset.sum_le_sum fun i hi ↦ hmult i hi
      _ = ∑ x ∈ points, F.rootMultiplicity x := by
        symm
        exact Finset.sum_map support nodes
          (fun x ↦ F.rootMultiplicity x)
  have hroots :=
    MatrixRootMultiplicity.sum_rootMultiplicity_le_natDegree (K := K) F points
  omega

theorem globalSpecialization_pderiv_R_eq_zero_of_taylor_divisibility
    {I : Type*} [Fintype I] (G : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (gamma : K) (nodes : I ↪ K)
    (support : Finset I) (multiplicity : I → ℕ)
    (hlocal : ∀ i ∈ support,
      (Polynomial.X : Polynomial K) ^ multiplicity i ∣
        Polynomial.taylor (nodes i)
          (globalSpecialization K P gamma
            (MvPolynomial.pderiv (2 : Fin 4) G)))
    (hdegree :
      (globalSpecialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) G)).natDegree <
          ∑ i ∈ support, multiplicity i) :
    globalSpecialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) G) = 0 := by
  let F := globalSpecialization K P gamma
    (MvPolynomial.pderiv (2 : Fin 4) G)
  by_cases hF : F = 0
  · exact hF
  apply eq_zero_of_rootMultiplicity_sum K F nodes support multiplicity
  · intro i hi
    exact rootMultiplicity_ge_of_taylor_dvd K F (nodes i)
      (multiplicity i) hF (hlocal i hi)
  · exact hdegree

private theorem localTranslation_flag_column
    (D w L s : ℕ) (x u0 u1 : K)
    (c : CoefficientIndex D w L s)
    (a : K) :
    localTranslation K x u0 u1
        (MvPolynomial.monomial
          (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
        (Polynomial.X * Polynomial.C (localA K) +
          Polynomial.C
            (seedAffine K u0 u1)) ^ c.1.val *
        Polynomial.C (localB K) ^ c.2.1.val *
        Polynomial.C (localZ K) ^ c.2.2.1.val := by
  rw [ContactTranslation.monomial_eq]
  simp [localTranslation, localVariables, localA, localB, localZ,
    seedAffine,
    ← MvPolynomial.C_mul_X_eq_monomial,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  left
  ring

private theorem localTranslation_flag_column_coeff
    (D w L s : ℕ) (x u0 u1 : K)
    (c : CoefficientIndex D w L s)
    (a : K) (r : ℕ) :
    (localTranslation K x u0 u1
      (MvPolynomial.monomial
        (columnExponent c) a)).coeff r =
      a • blockEntry
        K D w L s x u0 u1 c r := by
  have hfactor :
      localTranslation K x u0 u1
          (MvPolynomial.monomial
            (columnExponent c) a) =
        Polynomial.C (MvPolynomial.C a) *
          ((Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
            (Polynomial.X * Polynomial.C (localA K) +
              Polynomial.C
                (seedAffine K u0 u1)) ^ c.1.val *
            Polynomial.C
              (localB K ^ c.2.1.val * localZ K ^ c.2.2.1.val)) := by
    rw [localTranslation_flag_column K D w L s x u0 u1 c a]
    simp only [map_mul, map_pow]
    ring
  rw [hfactor, Polynomial.coeff_C_mul,
    ContactTranslation.coeff_shifted_affine_product]
  unfold blockEntry
  rw [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs with hfr
  · simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast]
    rw [show localMonomial K
        f.val c.2.1.val c.2.2.1.val =
      localA K ^ f.val * localB K ^ c.2.1.val *
        localZ K ^ c.2.2.1.val by
      rw [localMonomial,
        MvPolynomial.monomial_add_single,
        MvPolynomial.monomial_add_single,
        ← MvPolynomial.X_pow_eq_monomial]
      simp [localA, localB, localZ]]
    ring
  · simp

private theorem localTranslation_flag_reconstruct_coeff
    (D w L s : ℕ) (x u0 u1 : K)
    (theta : CoefficientIndex D w L s → K)
    (r : ℕ) :
    (localTranslation K x u0 u1
      (reconstruct
        K D w L s theta)).coeff r =
      ((extractBlock
        K D w L s x u0 u1 r theta) :
          Poly K) := by
  rw [reconstruct, map_sum,
    Polynomial.finsetSum_coeff]
  simp only [localTranslation_flag_column_coeff]
  change (∑ c : CoefficientIndex D w L s,
      theta c • blockEntry
        K D w L s x u0 u1 c r) =
    (((∑ c : CoefficientIndex D w L s,
      theta c • boundedBlockEntry
        K D w L s x u0 u1 c r) :
          coefficientBox
            K (min r L) L s) :
      Poly K)
  simp [boundedBlockEntry]

theorem HasContact.of_flag_kernel_reconstruct
    {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap
        K D w L s m nodes u0 u1)) (i : I) :
    HasContact K m
      (localTranslation K (nodes i) (u0 i) (u1 i)
        (reconstruct
          K D w L s theta)) := by
  intro r
  rw [localTranslation_flag_reconstruct_coeff]
  have hzero : constraintMap
      K D w L s m nodes u0 u1 theta = 0 := LinearMap.mem_ker.mp htheta
  have hequations : ∀ q : Fin m,
      contactJet K (m - q.val)
        ((extractBlock
          K D w L s (nodes i) (u0 i) (u1 i) q.val theta) :
            Poly K) = 0 := by
    intro q
    have happ := congrArg
      (fun target : GlobalTarget K I m L s ↦
        ((target i q) : Poly K)) hzero
    exact happ
  have hdiv := all_blocks_divisible_of_equations
    K D w L s m (nodes i) (u0 i) (u1 i) theta hequations r
  simpa [localDelta, localA, localB,
    slopeDifference] using hdiv

theorem scaled_contact_of_flag_kernel_reconstruct
    {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap
        K D w L s m nodes u0 u1)) (i : I) :
    (Polynomial.X : ScaledPolynomial K) ^ m ∣
      scaledLocalTranslation K (nodes i) (u0 i) (u1 i)
        (reconstruct
          K D w L s theta) := by
  rw [scaledLocalTranslation_eq_contactScaling]
  exact (HasContact.of_flag_kernel_reconstruct K D w L s m
    nodes u0 u1 theta htheta i).contactScaling_dvd K _ m

def HasExactScaledOrder (P : ScaledPolynomial K) (h : ℕ) : Prop :=
  P ≠ 0 ∧ P.natTrailingDegree = h

theorem scaled_pderiv_R_dvd_of_flag_kernel_factor
    {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u0 u1 : I → K)
    (theta : CoefficientIndex D w L s → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K D w L s m nodes u0 u1))
    (i : I) (G H : MvPolynomial (Fin 4) K) (h : ℕ)
    (hfactor : reconstruct K D w L s theta = G * H)
    (hH : HasExactScaledOrder K
      (scaledLocalTranslation K (nodes i) (u0 i) (u1 i) H) h) :
    (Polynomial.X : ScaledPolynomial K) ^ ((m - h) - 1) ∣
      scaledLocalTranslation K (nodes i) (u0 i) (u1 i)
        (MvPolynomial.pderiv (2 : Fin 4) G) := by
  apply pderiv_R_factor_scaled_order K
    (nodes i) (u0 i) (u1 i) G H m h
  · rw [← hfactor]
    exact scaled_contact_of_flag_kernel_reconstruct K
      D w L s m nodes u0 u1 theta htheta i
  · exact hH.1
  · exact hH.2

end
end ProximityPrize.SubmissionLower.RFreeDerivativeTransport
