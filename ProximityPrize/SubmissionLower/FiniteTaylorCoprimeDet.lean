import ProximityPrize.SubmissionLower.FiniteTaylorCore

namespace ProximityPrize.SubmissionLower.FiniteTaylorCoprimeDet

open Polynomial Matrix
open ProximityPrize.SubmissionLower.FiniteTaylorCore

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

variable {F : Type*} [Field F]

lemma vectorPolynomial_injective (h : ℕ) :
    Function.Injective (vectorPolynomial h :
      (Fin h → Polynomial F) → Polynomial (Polynomial F)) := by
  intro v w hvw
  funext i
  have := congrArg (fun P : Polynomial (Polynomial F) => P.coeff i.1) hvw
  simpa using this

/-- If `H` and `J` are coprime, multiplication by `J` in the finite free
quotient `(F[Z])[T]/(H)` has an integral inverse.  Hence its determinant is a
nonzero polynomial; no passage to roots or to an algebraic closure is needed. -/
theorem det_multiplicationMatrix_ne_zero_of_isCoprime
    (h : ℕ) (hh : 0 < h)
    (H J : Polynomial (Polynomial F))
    (hH : H.Monic) (hHdeg : H.natDegree = h)
    (hcoprime : IsCoprime H J) :
    (multiplicationMatrix h H J).det ≠ 0 := by
  rcases hcoprime with ⟨a, b, hab⟩
  let M := multiplicationMatrix h H J
  let B := multiplicationMatrix h H b
  have hright : ∀ v : Fin h → Polynomial F, M *ᵥ (B *ᵥ v) = v := by
    intro v
    let V := vectorPolynomial h v
    let BV := vectorPolynomial h (B *ᵥ v)
    have hdB : H ∣ b * V - BV := by
      exact multiplicationMatrix_divisibility h hh H hH hHdeg v b
    have hdJB : H ∣ J * (b * V - BV) := dvd_mul_of_dvd_right hdB J
    have hdBez : H ∣ J * b * V - V := by
      refine ⟨-a * V, ?_⟩
      have hcomm : J * b = b * J := mul_comm J b
      calc
        J * b * V - V = (b * J - 1) * V := by rw [hcomm]; ring
        _ = (-a * H) * V := by
          have heq : b * J - 1 = -a * H := by
            linear_combination hab
          rw [heq]
        _ = H * (-a * V) := by ring
    have hd : H ∣ J * BV - V := by
      have hd' := hdBez.sub hdJB
      convert hd' using 1 <;> ring
    have hrepr := multiplicationMatrix_represents_mul_mod
      h hh H hH hHdeg J (B *ᵥ v)
    have hmod : canonicalRemainder H (J * BV) = canonicalRemainder H V := by
      exact Polynomial.modByMonic_eq_of_dvd_sub hH hd
    have hVdeg : V.degree < H.degree := by
      rw [H.degree_eq_natDegree hH.ne_zero, hHdeg]
      exact vectorPolynomial_degree_lt h hh v
    have hVrem : canonicalRemainder H V = V :=
      canonicalRemainder_eq_self hH hVdeg
    apply vectorPolynomial_injective h
    calc
      vectorPolynomial h (M *ᵥ (B *ᵥ v)) = canonicalRemainder H (J * BV) :=
        hrepr.symm
      _ = canonicalRemainder H V := hmod
      _ = V := hVrem
  have hMB : M * B = 1 := by
    apply Matrix.ext
    intro i j
    have hv := congrFun (hright (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at hv
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.one_apply, Pi.single_apply, eq_comm] using hv
  have hdet := congrArg Matrix.det hMB
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  exact left_ne_zero_of_mul_eq_one hdet

section Map

variable {K : Type*} [Field K]

theorem map_companionMatrix (φ : Polynomial F →+* Polynomial K)
    (h : ℕ) (H : Polynomial (Polynomial F)) :
    RingHom.mapMatrix φ (companionMatrix h H) =
      companionMatrix h (H.map φ) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Polynomial.coeff_map]
  change φ ((if j.1 + 1 = i.1 then 1 else 0) -
      (if j.1 + 1 = h then H.coeff i.1 else 0)) = _
  by_cases hj : j.1 + 1 = h <;> simp [companionMatrix, hj]

theorem map_evalMatrix (φ : Polynomial F →+* Polynomial K)
    (h : ℕ) (P : Polynomial (Polynomial F))
    (A : Matrix (Fin h) (Fin h) (Polynomial F)) :
    RingHom.mapMatrix φ (evalMatrix P A) =
      evalMatrix (P.map φ) (RingHom.mapMatrix φ A) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      calc
        RingHom.mapMatrix φ (evalMatrix (P + Q) A) =
            RingHom.mapMatrix φ (evalMatrix P A + evalMatrix Q A) := by
              rw [evalMatrix_add]
        _ = RingHom.mapMatrix φ (evalMatrix P A) +
            RingHom.mapMatrix φ (evalMatrix Q A) := by rw [map_add]
        _ = evalMatrix (P.map φ) (RingHom.mapMatrix φ A) +
            evalMatrix (Q.map φ) (RingHom.mapMatrix φ A) := by rw [hP, hQ]
        _ = evalMatrix ((P + Q).map φ) (RingHom.mapMatrix φ A) := by
              rw [Polynomial.map_add, evalMatrix_add]
  | monomial n a =>
      rw [evalMatrix_monomial, Polynomial.map_monomial, evalMatrix_monomial]
      apply Matrix.ext
      intro i j
      change φ (a * (A ^ n) i j) = φ a *
        ((RingHom.mapMatrix φ A) ^ n) i j
      rw [map_mul]
      congr 1
      exact congrFun (congrFun (Matrix.map_pow A φ n) i) j

theorem map_multiplicationMatrix
    (φ : Polynomial F →+* Polynomial K)
    (h : ℕ) (H J : Polynomial (Polynomial F)) :
    RingHom.mapMatrix φ (multiplicationMatrix h H J) =
      multiplicationMatrix h (H.map φ) (J.map φ) := by
  rw [multiplicationMatrix, multiplicationMatrix, map_evalMatrix,
    map_companionMatrix]

theorem map_det_multiplicationMatrix
    (φ : Polynomial F →+* Polynomial K)
    (h : ℕ) (H J : Polynomial (Polynomial F)) :
    φ (multiplicationMatrix h H J).det =
      (multiplicationMatrix h (H.map φ) (J.map φ)).det := by
  rw [← map_multiplicationMatrix φ h H J]
  exact RingHom.map_det φ (multiplicationMatrix h H J)

/-- Coprimality after embedding the coefficient ring into a field already
forces the original multiplication determinant to be nonzero.  This is the
form used for integral monicizations: prove Bezout after passing to the
fraction field, then descend nonvanishing through the injective embedding. -/
theorem det_multiplicationMatrix_ne_zero_of_map_isCoprime
    {K : Type*} [Field K]
    (φ : Polynomial F →+* K) (hφ : Function.Injective φ)
    (h : ℕ) (hh : 0 < h)
    (H J : Polynomial (Polynomial F))
    (hH : H.Monic) (hHdeg : H.natDegree = h)
    (hcoprime : IsCoprime (H.map φ) (J.map φ)) :
    (multiplicationMatrix h H J).det ≠ 0 := by
  let ψ : Polynomial F →+* Polynomial K := Polynomial.C.comp φ
  have hψ : Function.Injective ψ := fun _ _ hab =>
    hφ (Polynomial.C_injective hab)
  have hcoprimeψ : IsCoprime (H.map ψ) (J.map ψ) := by
    have hmapped := hcoprime.map
      (Polynomial.mapRingHom (Polynomial.C : K →+* Polynomial K))
    simpa [ψ, Polynomial.map_map] using hmapped
  have hdetψ :
      (multiplicationMatrix h (H.map ψ) (J.map ψ)).det ≠ 0 := by
    apply det_multiplicationMatrix_ne_zero_of_isCoprime
      h hh (H.map ψ) (J.map ψ) (hH.map ψ)
    simpa [Polynomial.natDegree_map_eq_of_injective hψ] using hHdeg
    exact hcoprimeψ
  intro hdet
  apply hdetψ
  rw [← map_det_multiplicationMatrix ψ h H J, hdet, map_zero]

end Map

end

end ProximityPrize.SubmissionLower.FiniteTaylorCoprimeDet
