import ProximityPrize.SubmissionLower.RFreeJetCodimension
import ProximityPrize.SubmissionLower.RFreeDerivativeTransport

namespace ProximityPrize.SubmissionLower.RFreeScaledJetBridge

open scoped BigOperators
open ContactInterpolation ContactTranslation ContactRankKernel
open RFreeJetCodimension RFreeDerivativeTransport

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

def scaledDiagonalExponent (y r z : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 y + Finsupp.single 2 r + Finsupp.single 3 z

private def contactExponentMap : (Fin 4 →₀ ℕ) →+ (Fin 5 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 2) +
    Finsupp.single 2 (d 1) + Finsupp.single 3 (d 0) + Finsupp.single 4 (d 3)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' d e := by ext i; fin_cases i <;> simp [Finsupp.add_apply]; omega

private theorem contactExponentMap_injective :
    Function.Injective contactExponentMap := by
  intro d e h
  ext i
  fin_cases i
  · simpa [contactExponentMap] using congrArg (fun q : Fin 5 →₀ ℕ => q 3) h
  · simpa [contactExponentMap] using congrArg (fun q : Fin 5 →₀ ℕ => q 2) h
  · simpa [contactExponentMap] using congrArg (fun q : Fin 5 →₀ ℕ => q 1) h
  · simpa [contactExponentMap] using congrArg (fun q : Fin 5 →₀ ℕ => q 4) h

private def contactMonomialMap :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 5) K :=
  AddMonoidAlgebra.mapDomainAlgHom K K contactExponentMap

private def contactVariables : Fin 4 → MvPolynomial (Fin 5) K :=
  ![MvPolynomial.X 0 * MvPolynomial.X 3,
    MvPolynomial.X 0 * MvPolynomial.X 2,
    MvPolynomial.X 1, MvPolynomial.X 4]

private def contactSubstitution :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 5) K :=
  MvPolynomial.aeval (contactVariables (K := K))

private theorem contactSubstitution_eq_contactMonomialMap :
    contactSubstitution (K := K) = contactMonomialMap (K := K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp only [contactSubstitution, MvPolynomial.aeval_X] <;>
    simp [contactVariables, contactMonomialMap, contactExponentMap,
      MvPolynomial.X, MvPolynomial.monomial]

private def flatten (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) K) →ₐ[K]
      MvPolynomial (Fin (n + 1)) K :=
  (MvPolynomial.finSuccEquiv K n).symm.toAlgHom

@[simp] private theorem flatten_X (n : ℕ) :
    flatten (K := K) n Polynomial.X = MvPolynomial.X 0 := by
  apply (MvPolynomial.finSuccEquiv K n).injective
  simp [flatten, MvPolynomial.finSuccEquiv_X_zero]

@[simp] private theorem flatten_C (n : ℕ) (a : MvPolynomial (Fin n) K) :
    flatten (K := K) n (Polynomial.C a) = MvPolynomial.rename Fin.succ a := by
  apply (MvPolynomial.finSuccEquiv K n).injective
  rw [show (MvPolynomial.finSuccEquiv K n)
      (flatten (K := K) n (Polynomial.C a)) = Polynomial.C a by
    exact AlgEquiv.apply_symm_apply _ _]
  induction a using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simpa only [map_add, hp, hq]
  | mul_X p i hp =>
      simpa only [map_mul, MvPolynomial.rename_X,
        MvPolynomial.finSuccEquiv_X_succ, hp]

private theorem flattened_translation_eq
    (x u0 u1 : K) (Q : MvPolynomial (Fin 4) K) :
    flatten (K := K) 4 (scaledLocalTranslation K x u0 u1 Q) =
      contactSubstitution (K := K)
        (flatten (K := K) 3 (deltaHomogenizedTranslation x u0 u1 Q)) := by
  have hhom :
      (flatten (K := K) 4).comp (scaledLocalTranslation K x u0 u1) =
        (contactSubstitution (K := K)).comp
          ((flatten (K := K) 3).comp (deltaHomogenizedTranslation x u0 u1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [scaledLocalTranslation, scaledLocalVariables, scaledB, scaledD,
        scaledU, scaledZ, contactSubstitution, contactVariables,
        deltaHomogenizedTranslation, homogenizedTranslation,
        translationVariables, RFreeJetCodimension.deltaShift,
        seedAffine, ← MvPolynomial.C_mul_X_eq_monomial] <;> ring
  exact DFunLike.congr_fun hhom Q

theorem delta_scaled_diagonal_coeff
    (x u0 u1 : K) (Q : MvPolynomial (Fin 4) K) (y r z : ℕ) :
    MvPolynomial.coeff (diagonalLocalExponent y z)
        ((deltaHomogenizedTranslation x u0 u1 Q).coeff r) =
      MvPolynomial.coeff (scaledDiagonalExponent y r z)
        ((scaledLocalTranslation K x u0 u1 Q).coeff r) := by
  let localPoly := flatten (K := K) 3 (deltaHomogenizedTranslation x u0 u1 Q)
  let scaledPoly := flatten (K := K) 4 (scaledLocalTranslation K x u0 u1 Q)
  have hflat : scaledPoly = contactMonomialMap (K := K) localPoly := by
    change flatten (K := K) 4 (scaledLocalTranslation K x u0 u1 Q) = _
    rw [flattened_translation_eq, contactSubstitution_eq_contactMonomialMap]
  have hexponent :
      contactExponentMap ((diagonalLocalExponent y z).cons r) =
        (scaledDiagonalExponent y r z).cons r := by
    have hs1 : ((diagonalLocalExponent y z).cons r) (1 : Fin 4) = 0 := by
      rw [show (1 : Fin 4) = (0 : Fin 3).succ by decide, Finsupp.cons_succ]
      simp [diagonalLocalExponent]
    have hs2 : ((diagonalLocalExponent y z).cons r) (2 : Fin 4) = y := by
      rw [show (2 : Fin 4) = (1 : Fin 3).succ by decide, Finsupp.cons_succ]
      simp [diagonalLocalExponent]
    have hs3 : ((diagonalLocalExponent y z).cons r) (3 : Fin 4) = z := by
      rw [show (3 : Fin 4) = (2 : Fin 3).succ by decide, Finsupp.cons_succ]
      simp [diagonalLocalExponent]
    have ht1 : ((scaledDiagonalExponent y r z).cons r) (1 : Fin 5) = y := by
      rw [show (1 : Fin 5) = (0 : Fin 4).succ by decide, Finsupp.cons_succ]
      simp [scaledDiagonalExponent]
    have ht2 : ((scaledDiagonalExponent y r z).cons r) (2 : Fin 5) = 0 := by
      rw [show (2 : Fin 5) = (1 : Fin 4).succ by decide, Finsupp.cons_succ]
      simp [scaledDiagonalExponent]
    have ht3 : ((scaledDiagonalExponent y r z).cons r) (3 : Fin 5) = r := by
      rw [show (3 : Fin 5) = (2 : Fin 4).succ by decide, Finsupp.cons_succ]
      simp [scaledDiagonalExponent]
    have ht4 : ((scaledDiagonalExponent y r z).cons r) (4 : Fin 5) = z := by
      rw [show (4 : Fin 5) = (3 : Fin 4).succ by decide, Finsupp.cons_succ]
      simp [scaledDiagonalExponent]
    ext i
    fin_cases i <;>
      simp [contactExponentMap, hs1, hs2, hs3, ht1, ht2, ht3, ht4]
  calc
    MvPolynomial.coeff (diagonalLocalExponent y z)
        ((deltaHomogenizedTranslation x u0 u1 Q).coeff r) =
      MvPolynomial.coeff ((diagonalLocalExponent y z).cons r) localPoly := by
        simpa [localPoly, flatten] using
          MvPolynomial.finSuccEquiv_coeff_coeff
            (diagonalLocalExponent y z) localPoly r
    _ = MvPolynomial.coeff ((scaledDiagonalExponent y r z).cons r)
        (contactMonomialMap (K := K) localPoly) := by
      rw [← hexponent]
      change (AddMonoidAlgebra.coeff localPoly)
          ((diagonalLocalExponent y z).cons r) =
        Finsupp.mapDomain contactExponentMap (AddMonoidAlgebra.coeff localPoly)
          (contactExponentMap ((diagonalLocalExponent y z).cons r))
      rw [Finsupp.mapDomain_apply contactExponentMap_injective]
    _ = MvPolynomial.coeff ((scaledDiagonalExponent y r z).cons r) scaledPoly := by
      rw [hflat]
    _ = MvPolynomial.coeff (scaledDiagonalExponent y r z)
        ((scaledLocalTranslation K x u0 u1 Q).coeff r) := by
      symm
      simpa [scaledPoly, flatten] using
        MvPolynomial.finSuccEquiv_coeff_coeff
          (scaledDiagonalExponent y r z) scaledPoly r

theorem mem_ker_rfreeSelectedJetMap_of_scaled_contact
    (D w L : ℕ) (points : Finset K) (h : K → ℕ) (u0 u1 : K → K)
    (Q : globalCoefficientBox K D w L 0)
    (hscaled : ∀ x : points,
      (Polynomial.X : ScaledPolynomial K) ^ h (x : K) ∣
        scaledLocalTranslation K (x : K) (u0 x) (u1 x) Q.1) :
    Q ∈ LinearMap.ker (rfreeSelectedJetMap D w L points h u0 u1) := by
  rw [LinearMap.mem_ker]
  funext y z x k
  change MvPolynomial.coeff (diagonalLocalExponent y.val z.val)
      ((deltaHomogenizedTranslation (x : K) (u0 x) (u1 x) Q.1).coeff
        (y.val + k.val)) = 0
  rw [delta_scaled_diagonal_coeff]
  have hlt : y.val + k.val < h (x : K) := by
    simpa [Nat.add_comm] using Nat.add_lt_of_lt_sub k.isLt
  have hzero := (Polynomial.X_pow_dvd_iff.mp (hscaled x))
    (y.val + k.val) hlt
  rw [hzero, MvPolynomial.coeff_zero]

end
end ProximityPrize.SubmissionLower.RFreeScaledJetBridge
