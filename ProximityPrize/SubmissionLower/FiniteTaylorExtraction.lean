import ProximityPrize.SubmissionLower.FiniteTaylorCore

/-!
# Finite Taylor extraction and specialization

The input branch polynomial need not be monic in its `Y` variable.  If its
`Y`-degree is `h` and its leading coefficient is `W(Z)`, we first replace it by

`Hbar(T) = W^(h-1) H(T/W)
         = T^h + ∑_{i<h} H_i W^(h-1-i) T^i`.

This is integral over `F[Z]`; no rational-function denominator is introduced.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorExtraction

open scoped BigOperators
open Polynomial Matrix
open FiniteTaylorCore

noncomputable section

set_option maxHeartbeats 50000

variable {F : Type*} [Field F]

/-- Integral scaling in an outer polynomial variable:
`W^d R(T/W) = Σ_i R_i W^(d-i) T^i`. -/
def integralScale {A : Type*} [CommRing A] (W : A) (R : Polynomial A) :
    Polynomial A :=
  let d := R.natDegree
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i (R.coeff i * W ^ (d - i))

theorem eval₂_integralScale {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (W : A) (R : Polynomial A) (y : B) :
    Polynomial.eval₂ f (f W * y) (integralScale W R) =
      f W ^ R.natDegree * Polynomial.eval₂ f y R := by
  classical
  unfold integralScale
  change (Polynomial.eval₂RingHom f (f W * y))
      (∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.monomial i (R.coeff i * W ^ (R.natDegree - i))) = _
  rw [map_sum]
  rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ R.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  have hexp : R.natDegree - i + i = R.natDegree := by omega
  rw [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_monomial]
  simp only [map_mul, map_pow, mul_pow]
  calc
    f (R.coeff i) * f W ^ (R.natDegree - i) * (f W ^ i * y ^ i) =
        f (R.coeff i) *
          (f W ^ (R.natDegree - i) * f W ^ i) * y ^ i := by ring
    _ = f (R.coeff i) * f W ^ R.natDegree * y ^ i := by
      rw [← pow_add, hexp]
    _ = f W ^ R.natDegree * (f (R.coeff i) * y ^ i) := by ring

theorem integralScale_root {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (W : A) (R : Polynomial A) (y : B)
    (hy : Polynomial.eval₂ f y R = 0) :
    Polynomial.eval₂ f (f W * y) (integralScale W R) = 0 := by
  rw [eval₂_integralScale, hy, mul_zero]

/-! Finite-order implicit-function identities.  Everything is stated for
ordinary polynomials: only finitely many coefficients are ever used, and this
keeps the submission inside the benchmark's fixed import closure. -/

theorem polynomial_coeff_mul_eq_zero_of_orders {A : Type*} [CommRing A]
    {m : Nat} (u v : Polynomial A) (a b : Nat)
    (hab : m < a + b) (hu : ∀ i < a, u.coeff i = 0)
    (hv : ∀ i < b, v.coeff i = 0) :
    (u * v).coeff m = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rcases lt_or_ge p.1 a with h1 | h1
  · rw [hu p.1 h1, zero_mul]
  · have h2 : p.2 < b := by omega
    rw [hv p.2 h2, mul_zero]

theorem polynomial_coeff_mul_of_low_order {A : Type*} [CommRing A]
    (n : Nat) (P δ : Polynomial A)
    (hδ : ∀ i < n, δ.coeff i = 0) :
    (P * δ).coeff n = P.coeff 0 * δ.coeff n := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (0, n)]
  · intro b hb hbne
    have hmem : b.1 + b.2 = n := Finset.mem_antidiagonal.mp hb
    have hb2 : b.2 < n := by
      rcases Nat.eq_zero_or_pos b.1 with h | h
      · exfalso
        apply hbne
        ext
        · simp [h]
        · simp
          omega
      · omega
    rw [hδ b.2 hb2, mul_zero]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

theorem polynomial_eval₂_remainder_low_order {A B : Type*}
    [CommRing A] [CommRing B] (n : Nat) (φ : A →+* Polynomial B)
    (Γ δ : Polynomial B) (hδ : ∀ i < n, δ.coeff i = 0)
    (p : Polynomial A) : ∀ i < 2 * n,
      (Polynomial.eval₂ φ (Γ + δ) p - Polynomial.eval₂ φ Γ p -
        Polynomial.eval₂ φ Γ p.derivative * δ).coeff i = 0 := by
  induction p using Polynomial.induction_on with
  | C a =>
      intro i hi
      simp [Polynomial.derivative_C]
  | add p q hp hq =>
      intro i hi
      have e1 := hp i hi
      have e2 := hq i hi
      simp only [Polynomial.eval₂_add, Polynomial.derivative_add, add_mul,
        Polynomial.coeff_add, Polynomial.coeff_sub] at *
      linear_combination e1 + e2
  | monomial m a hp =>
      intro i hi
      set q : Polynomial A := Polynomial.C a * Polynomial.X ^ m with hq
      have hmulX : Polynomial.C a * Polynomial.X ^ (m + 1) =
          q * Polynomial.X := by rw [hq]; ring
      rw [hmulX]
      have hderiv : (q * Polynomial.X).derivative =
          q.derivative * Polynomial.X + q := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [hderiv]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_add]
      set u := Polynomial.eval₂ φ Γ q
      set up := Polynomial.eval₂ φ (Γ + δ) q
      set d := Polynomial.eval₂ φ Γ q.derivative
      have hrewrite : up * (Γ + δ) - u * Γ - (d * Γ + u) * δ =
          d * (δ * δ) + (up - u - d * δ) * (Γ + δ) := by ring
      rw [hrewrite]
      have h1 : (d * (δ * δ)).coeff i = 0 := by
        apply polynomial_coeff_mul_eq_zero_of_orders d (δ * δ) 0 (2 * n)
          (by omega)
        · intro j hj
          omega
        · intro j hj
          exact polynomial_coeff_mul_eq_zero_of_orders δ δ n n (by omega) hδ hδ
      have h2 : ((up - u - d * δ) * (Γ + δ)).coeff i = 0 := by
        apply polynomial_coeff_mul_eq_zero_of_orders
          (up - u - d * δ) (Γ + δ) (2 * n) 0 (by omega)
        · intro j hj
          exact hp j hj
        · intro j hj
          omega
      rw [Polynomial.coeff_add, h1, h2, add_zero]

theorem polynomial_coeff_eval₂_split {A B : Type*}
    [CommRing A] [CommRing B] (n : Nat) (hn : 1 ≤ n)
    (φ : A →+* Polynomial B) (Γ δ : Polynomial B)
    (hδ : ∀ i < n, δ.coeff i = 0) (p : Polynomial A) :
    (Polynomial.eval₂ φ (Γ + δ) p).coeff n =
      (Polynomial.eval₂ φ Γ p).coeff n +
        (Polynomial.eval₂ φ Γ p.derivative).coeff 0 * δ.coeff n := by
  have hrem := polynomial_eval₂_remainder_low_order n φ Γ δ hδ p n (by omega)
  simp only [Polynomial.coeff_sub] at hrem
  rw [polynomial_coeff_mul_of_low_order n _ δ hδ] at hrem
  linear_combination hrem

/-- Polynomial form of the finite implicit-function coefficient identity.
If `g` is an exact polynomial root of `P(S,T)` and `Γ` agrees with `g`
strictly below order `n`, then the order-`n` coefficient is determined by
the linearized equation.  Notice that no injectivity in a quotient ring is
used here: this is an equality in the scalar coefficient field. -/
theorem polynomial_root_taylor_coefficient_equation {A : Type*} [Field A]
    (n : Nat) (hn : 1 ≤ n) (P : Polynomial (Polynomial A))
    (g Γ : Polynomial A)
    (hroot : Polynomial.eval₂ (RingHom.id (Polynomial A)) g P = 0)
    (hlow : ∀ i < n, Γ.coeff i = g.coeff i)
    (hnextzero : Γ.coeff n = 0) :
    (Polynomial.eval₂ (RingHom.id (Polynomial A)) Γ P.derivative).coeff 0 *
        g.coeff n =
      -(Polynomial.eval₂ (RingHom.id (Polynomial A)) Γ P).coeff n := by
  let δ : Polynomial A := g - Γ
  have hδ : ∀ i < n, δ.coeff i = 0 := by
    intro i hi
    simp only [δ, Polynomial.coeff_sub]
    rw [← hlow i hi, sub_self]
  have hsplit := polynomial_coeff_eval₂_split n hn
    (RingHom.id (Polynomial A)) Γ δ hδ P
  have hsum : Γ + δ = g := by
    simp [δ]
  rw [hsum] at hsplit
  rw [hroot] at hsplit
  simp only [Polynomial.coeff_zero] at hsplit
  have hδn : δ.coeff n = g.coeff n := by
    simp [δ, hnextzero]
  rw [hδn] at hsplit
  change 0 = _ + _ at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit.symm

/-- Taylor polynomial through order `t`. -/
def truncatePolynomial {A : Type*} [Semiring A] (t : Nat)
    (g : Polynomial A) : Polynomial A :=
  ∑ i : Fin (t + 1), Polynomial.monomial i.1 (g.coeff i.1)

theorem truncatePolynomial_coeff_of_le {A : Type*} [Semiring A]
    (t i : Nat) (g : Polynomial A) (hi : i ≤ t) :
    (truncatePolynomial t g).coeff i = g.coeff i := by
  classical
  unfold truncatePolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single ⟨i, by omega⟩]
  · simp
  · intro b hb hne
    simp only [if_neg (by
      intro h
      apply hne
      exact Fin.ext h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem truncatePolynomial_coeff_of_lt {A : Type*} [Semiring A]
    (t i : Nat) (g : Polynomial A) (hi : i < t + 1) :
    (truncatePolynomial t g).coeff i = g.coeff i :=
  truncatePolynomial_coeff_of_le t i g (by omega)

theorem truncatePolynomial_coeff_of_gt {A : Type*} [Semiring A]
    (t i : Nat) (g : Polynomial A) (hi : t < i) :
    (truncatePolynomial t g).coeff i = 0 := by
  classical
  unfold truncatePolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_neg (by omega)]

theorem truncatePolynomial_eq_self {A : Type*} [Semiring A]
    (t : Nat) (g : Polynomial A) (hdeg : g.natDegree ≤ t) :
    truncatePolynomial t g = g := by
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ t
  · exact truncatePolynomial_coeff_of_le t i g hi
  · have hgi : g.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))
    rw [hgi]
    classical
    unfold truncatePolynomial
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by omega)]

/-- Integral monicization in the scaled variable `T = W Y`. -/
def integralMonicize (H : Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  let h := H.natDegree
  let W := H.leadingCoeff
  Polynomial.monomial h 1 +
    ∑ i ∈ Finset.range h,
      Polynomial.monomial i (H.coeff i * W ^ (h - 1 - i))

theorem integralMonicize_coeff_top (H : Polynomial (Polynomial F)) :
    (integralMonicize H).coeff H.natDegree = 1 := by
  classical
  simp only [integralMonicize, coeff_add, coeff_monomial,
    Polynomial.finsetSum_coeff]
  simp

theorem integralMonicize_natDegree_le (H : Polynomial (Polynomial F)) :
    (integralMonicize H).natDegree ≤ H.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  classical
  simp only [integralMonicize, coeff_add, coeff_monomial,
    Polynomial.finsetSum_coeff]
  have hne : H.natDegree ≠ n := by omega
  simp only [if_neg hne]
  rw [zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  have hilt : i < H.natDegree := Finset.mem_range.mp hi
  have hin : i ≠ n := by omega
  simp [hin]

theorem integralMonicize_monic (H : Polynomial (Polynomial F)) :
    (integralMonicize H).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one H.natDegree
    (integralMonicize_natDegree_le H) (integralMonicize_coeff_top H)

theorem integralMonicize_natDegree (H : Polynomial (Polynomial F)) :
    (integralMonicize H).natDegree = H.natDegree := by
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (integralMonicize_natDegree_le H) (by
      rw [integralMonicize_coeff_top]
      exact one_ne_zero)

/-- Specialize the `Z` coefficients at `z`. -/
def specializeZ (z : F) (P : Polynomial (Polynomial F)) : Polynomial F :=
  P.map (Polynomial.evalRingHom z)

/-- Evaluate a quotient polynomial in `F[Z][T]` at `(z,y)`. -/
def evalZT (z y : F) : Polynomial (Polynomial F) →+* F :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y

theorem evalZT_eq_specializeZ_eval (z y : F)
    (P : Polynomial (Polynomial F)) :
    evalZT z y P = (specializeZ z P).eval y := by
  simp [evalZT, specializeZ, Polynomial.eval_map]

theorem integralMonicize_specialize_eval (H : Polynomial (Polynomial F))
    (hh : 0 < H.natDegree) (z y : F) :
    (specializeZ z (integralMonicize H)).eval (H.leadingCoeff.eval z * y) =
      (H.leadingCoeff.eval z) ^ (H.natDegree - 1) *
        (specializeZ z H).eval y := by
  classical
  unfold specializeZ
  rw [Polynomial.eval_map, Polynomial.eval_map]
  unfold integralMonicize
  rw [Polynomial.eval₂_add, Polynomial.eval₂_monomial]
  have hevalsum :
      Polynomial.eval₂ (Polynomial.evalRingHom z) (H.leadingCoeff.eval z * y)
          (∑ i ∈ Finset.range H.natDegree,
            Polynomial.monomial i
              (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i))) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.eval₂ (Polynomial.evalRingHom z)
            (H.leadingCoeff.eval z * y)
            (Polynomial.monomial i
              (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i))) := by
    change (Polynomial.eval₂RingHom (Polynomial.evalRingHom z)
      (H.leadingCoeff.eval z * y))
        (∑ i ∈ Finset.range H.natDegree,
          Polynomial.monomial i
            (H.coeff i * H.leadingCoeff ^ (H.natDegree - 1 - i))) = _
    exact map_sum _ _ _
  rw [hevalsum]
  simp_rw [Polynomial.eval₂_monomial]
  simp only [map_one, one_mul, map_mul, map_pow]
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hlower (i : Nat) (hi : i < H.natDegree) :
      (H.coeff i).eval z * (H.leadingCoeff.eval z) ^
          (H.natDegree - 1 - i) *
          (H.leadingCoeff.eval z * y) ^ i =
        (H.leadingCoeff.eval z) ^ (H.natDegree - 1) *
          ((H.coeff i).eval z * y ^ i) := by
    have hexp : H.natDegree - 1 - i + i = H.natDegree - 1 := by omega
    rw [mul_pow]
    calc
      (H.coeff i).eval z * (H.leadingCoeff.eval z) ^
            (H.natDegree - 1 - i) *
            ((H.leadingCoeff.eval z) ^ i * y ^ i) =
          (H.coeff i).eval z *
            ((H.leadingCoeff.eval z) ^ (H.natDegree - 1 - i) *
              (H.leadingCoeff.eval z) ^ i) * y ^ i := by ring
      _ = (H.coeff i).eval z *
            (H.leadingCoeff.eval z) ^ (H.natDegree - 1) * y ^ i := by
          rw [← pow_add, hexp]
      _ = _ := by ring
  have hsum :
      (∑ i ∈ Finset.range H.natDegree,
          (H.coeff i).eval z * (H.leadingCoeff.eval z) ^
            (H.natDegree - 1 - i) *
            (H.leadingCoeff.eval z * y) ^ i) =
        (H.leadingCoeff.eval z) ^ (H.natDegree - 1) *
          ∑ i ∈ Finset.range H.natDegree, (H.coeff i).eval z * y ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hlower i (Finset.mem_range.mp hi)
  change
    (H.leadingCoeff.eval z * y) ^ H.natDegree +
        (∑ i ∈ Finset.range H.natDegree,
          (H.coeff i).eval z * (H.leadingCoeff.eval z) ^
            (H.natDegree - 1 - i) *
            (H.leadingCoeff.eval z * y) ^ i) =
      (H.leadingCoeff.eval z) ^ (H.natDegree - 1) *
        ((∑ i ∈ Finset.range H.natDegree,
          (H.coeff i).eval z * y ^ i) +
          (H.coeff H.natDegree).eval z * y ^ H.natDegree)
  rw [hsum]
  rw [show H.coeff H.natDegree = H.leadingCoeff from Polynomial.coeff_natDegree]
  rw [mul_pow]
  have hpow : (H.leadingCoeff.eval z) ^ H.natDegree =
      (H.leadingCoeff.eval z) ^ (H.natDegree - 1) * H.leadingCoeff.eval z := by
    conv_lhs => rw [show H.natDegree = (H.natDegree - 1) + 1 by omega,
      pow_succ]
  rw [hpow]
  ring

/-- Every specialized root of `H` gives a specialized root of the integral
monicization after scaling by the specialized leading coefficient.  The
converse is used only away from the leading-coefficient exception. -/
theorem integralMonicize_specialized_root (H : Polynomial (Polynomial F))
    (hh : 0 < H.natDegree) (z y : F)
    (hy : (specializeZ z H).eval y = 0) :
    (specializeZ z (integralMonicize H)).eval
        (H.leadingCoeff.eval z * y) = 0 := by
  rw [integralMonicize_specialize_eval H hh z y, hy, mul_zero]

/-- Away from `W(z)=0`, the scaled monicized equation is equivalent to the
original specialized equation. -/
theorem integralMonicize_specialized_root_iff (H : Polynomial (Polynomial F))
    (hh : 0 < H.natDegree) (z y : F) (hW : H.leadingCoeff.eval z ≠ 0) :
    (specializeZ z (integralMonicize H)).eval
          (H.leadingCoeff.eval z * y) = 0 ↔
      (specializeZ z H).eval y = 0 := by
  rw [integralMonicize_specialize_eval H hh z y]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hW))

/-- The additional exception introduced by integral monicization is exactly a
root of `W=leadingCoeff H`, hence costs at most `deg W` field points. -/
theorem card_integralMonicize_leadingCoeff_exceptions [Fintype F] [DecidableEq F]
    (H : Polynomial (Polynomial F)) (hW : H.leadingCoeff ≠ 0) :
    (Finset.univ.filter fun z : F => H.leadingCoeff.eval z = 0).card ≤
      H.leadingCoeff.natDegree := by
  classical
  let bad := Finset.univ.filter fun z : F => H.leadingCoeff.eval z = 0
  have hroots : bad.val ⊆ H.leadingCoeff.roots := by
    intro z hz
    exact (Polynomial.mem_roots hW).mpr (Finset.mem_filter.mp hz).2
  exact Polynomial.card_le_degree_of_subset_roots hroots

theorem card_integralMonicize_leadingCoeff_exceptions_le_72
    [Fintype F] [DecidableEq F] (H : Polynomial (Polynomial F))
    (hW : H.leadingCoeff ≠ 0) (hWdeg : H.leadingCoeff.natDegree ≤ 72) :
    (Finset.univ.filter fun z : F => H.leadingCoeff.eval z = 0).card ≤ 72 :=
  (card_integralMonicize_leadingCoeff_exceptions H hW).trans hWdeg

@[simp] theorem specializeZ_coeff (z : F) (P : Polynomial (Polynomial F)) (i : Nat) :
    (specializeZ z P).coeff i = (P.coeff i).eval z := by
  simp [specializeZ]

theorem specializeZ_canonicalRemainder (z : F)
    (H P : Polynomial (Polynomial F)) (hH : H.Monic) :
    specializeZ z (canonicalRemainder H P) =
      (specializeZ z P) %ₘ (specializeZ z H) := by
  unfold specializeZ canonicalRemainder
  exact Polynomial.map_modByMonic (Polynomial.evalRingHom z) hH

theorem eval_specializeZ_canonicalRemainder_at_root (z y : F)
    (H P : Polynomial (Polynomial F))
    (hy : (specializeZ z H).eval y = 0) :
    (specializeZ z (canonicalRemainder H P)).eval y =
      (specializeZ z P).eval y := by
  obtain ⟨Q, hQ⟩ := canonicalRemainder_congruent P (H := H)
  have heq := congrArg (evalZT z y) hQ
  have hy' : evalZT z y H = 0 := by
    simpa [evalZT, specializeZ, Polynomial.eval_map] using hy
  rw [map_sub, map_mul, hy', zero_mul] at heq
  simpa [evalZT_eq_specializeZ_eval] using sub_eq_zero.mp heq

/-- One division-free Taylor/Cramer numerator step. -/
def cramerStep {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (b : Fin n → Polynomial F) : Fin n → Polynomial F :=
  M.adjugate *ᵥ b

/-- Scalar form of the universal Cramer step.  Unlike vector injectivity, this
is exactly what one specialized root uses: evaluating at a root of `H` turns
the quotient identity into a scalar equation. -/
theorem scalar_cramerStep_equation_at_root (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (J : Polynomial (Polynomial F)) (b : Fin h → Polynomial F)
    (z y : F) (hy : (specializeZ z H).eval y = 0) :
    (specializeZ z J).eval y *
        (specializeZ z (vectorPolynomial h
          (cramerStep (multiplicationMatrix h H J) b))).eval y =
      (multiplicationMatrix h H J).det.eval z *
        (specializeZ z (vectorPolynomial h b)).eval y := by
  let M := multiplicationMatrix h H J
  let q := M.det
  have hbez := multiplicationMatrix_adjugate_bezout h hh H hH hHdeg J b
  dsimp only at hbez
  have heval := congrArg (fun S : Polynomial (Polynomial F) =>
    (specializeZ z S).eval y) hbez
  rw [eval_specializeZ_canonicalRemainder_at_root z y H _ hy] at heval
  simpa [cramerStep, specializeZ, Polynomial.eval_map,
    Polynomial.eval_mul] using heval

theorem scalar_cramerStep_specialization_unique_succ (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic) (hHdeg : H.natDegree = h)
    (J : Polynomial (Polynomial F)) (b : Fin h → Polynomial F)
    (z y a : F) (hy : (specializeZ z H).eval y = 0)
    (hq : (multiplicationMatrix h H J).det.eval z ≠ 0)
    (hJ : (specializeZ z J).eval y ≠ 0) (s : Nat)
    (hsolve : (specializeZ z J).eval y *
        ((multiplicationMatrix h H J).det.eval z ^ (2 * s) * a) =
      (specializeZ z (vectorPolynomial h b)).eval y) :
    a = ((multiplicationMatrix h H J).det.eval z ^ (2 * s + 1))⁻¹ *
      (specializeZ z (vectorPolynomial h
        (cramerStep (multiplicationMatrix h H J) b))).eval y := by
  have hcramer := scalar_cramerStep_equation_at_root h hh H hH hHdeg J b z y hy
  let qz := (multiplicationMatrix h H J).det.eval z
  let jz := (specializeZ z J).eval y
  let N := (specializeZ z (vectorPolynomial h
    (cramerStep (multiplicationMatrix h H J) b))).eval y
  let B := (specializeZ z (vectorPolynomial h b)).eval y
  have hsolve' : jz * (qz ^ (2 * s) * a) = B := by
    simpa [jz, qz, B] using hsolve
  have hN : N = qz ^ (2 * s + 1) * a := by
    have hc : jz * N = jz * (qz ^ (2 * s + 1) * a) := by
      calc
        jz * N = qz * B := by simpa [jz, N, qz, B] using hcramer
        _ = qz * (jz * (qz ^ (2 * s) * a)) := by rw [hsolve']
        _ = jz * (qz ^ (2 * s + 1) * a) := by rw [pow_succ']; ring
    exact (mul_left_cancel₀ hJ hc)
  change a = (qz ^ (2 * s + 1))⁻¹ * N
  rw [hN]
  simp [qz, hq]

/-- Entrywise specialization of a polynomial matrix. -/
def specializeMatrix {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F)) : Matrix (Fin n) (Fin n) F :=
  M.map (Polynomial.evalRingHom z)

/-- Entrywise specialization of a polynomial vector. -/
def specializeVector {n : Nat} (z : F)
    (v : Fin n → Polynomial F) : Fin n → F :=
  fun i => (v i).eval z

@[simp] theorem specializeVector_apply {n : Nat} (z : F)
    (v : Fin n → Polynomial F) (i : Fin n) :
    specializeVector z v i = (v i).eval z := rfl

theorem specializeMatrix_mulVec {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (v : Fin n → Polynomial F) :
    specializeMatrix z M *ᵥ specializeVector z v =
      specializeVector z (M *ᵥ v) := by
  funext i
  change
    (∑ j, (Polynomial.evalRingHom z) (M i j) *
      (Polynomial.evalRingHom z) (v j)) =
      (Polynomial.evalRingHom z) (∑ j, M i j * v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]

theorem specializeVector_smul {n : Nat} (z : F) (a : Polynomial F)
    (v : Fin n → Polynomial F) :
    specializeVector z (a • v) = a.eval z • specializeVector z v := by
  funext i
  simp [specializeVector, smul_eq_mul]

theorem det_specializeMatrix {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F)) :
    (specializeMatrix z M).det = M.det.eval z := by
  exact (RingHom.map_det (Polynomial.evalRingHom z) M).symm

theorem adjugate_specializeMatrix {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F)) :
    M.adjugate.map (Polynomial.evalRingHom z) =
      (specializeMatrix z M).adjugate := by
  exact RingHom.map_adjugate (Polynomial.evalRingHom z) M

/-- Division-free Cramer's rule after specialization.  Any specialized
solution has numerator `adj(M)b` and scalar denominator `det(M)`. -/
theorem specialized_solution_cramer {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (b : Fin n → Polynomial F) (x : Fin n → F)
    (hx : specializeMatrix z M *ᵥ x = specializeVector z b) :
    specializeVector z (M.adjugate *ᵥ b) = M.det.eval z • x := by
  calc
    specializeVector z (M.adjugate *ᵥ b) =
        specializeMatrix z M.adjugate *ᵥ specializeVector z b := by
      rw [specializeMatrix_mulVec]
    _ = (specializeMatrix z M).adjugate *ᵥ specializeVector z b := by
      rw [specializeMatrix, adjugate_specializeMatrix]
    _ = (specializeMatrix z M).adjugate *ᵥ
        (specializeMatrix z M *ᵥ x) := by rw [hx]
    _ = (specializeMatrix z M).det • x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    _ = M.det.eval z • x := by rw [det_specializeMatrix]

theorem vectorHeight_cramerStep_le {n E D : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (b : Fin n → Polynomial F)
    (hM : ∀ i j, (M i j).natDegree ≤ E)
    (hb : vectorHeight b ≤ D) :
    vectorHeight (cramerStep M b) ≤ n * E + D := by
  have hadj : matrixHeight M.adjugate ≤ n * E := by
    rw [matrixHeight_le_iff]
    exact natDegree_adjugate_entry_le M hM
  exact (vectorHeight_mulVec_le M.adjugate b).trans
    (Nat.add_le_add hadj hb)

theorem vectorHeight_cramerStep_multiplicationMatrix_le (h : Nat)
    (H J : Polynomial (Polynomial F)) (b : Fin h → Polynomial F) :
    vectorHeight (cramerStep (multiplicationMatrix h H J) b) ≤
      h * (polyHeight J + J.natDegree * polyHeight H) + vectorHeight b := by
  apply vectorHeight_cramerStep_le
  · intro i j
    exact (natDegree_entry_le_matrixHeight (multiplicationMatrix h H J) i j).trans
      (matrixHeight_multiplicationMatrix_le h H J)
  · exact le_rfl

/-! ## Concrete finite Taylor coefficient extraction -/

/-- Polynomials in `F[Z][X][T]`, with `T` outermost. -/
abbrev TriPolynomial (F : Type*) [Semiring F] :=
  Polynomial (Polynomial (Polynomial F))

/-- Substitute `X := x₀ + S` in an `F[Z][X]` coefficient. -/
def shiftXCoefficient (x₀ : F) :
    Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
  Polynomial.eval₂RingHom Polynomial.C
    (Polynomial.X + Polynomial.C (Polynomial.C x₀))

/-- Substitute `X := x₀ + S` coefficientwise in `R(Z,X,T)`. -/
def shiftX (x₀ : F) (R : TriPolynomial F) : TriPolynomial F :=
  R.map (shiftXCoefficient x₀)

/-- Specialize `Z=z` after translating `X=x₀+S`; the result is a polynomial
in `T` whose coefficients are polynomials in the Taylor variable `S`. -/
def specializeShiftX (x₀ z : F) (R : TriPolynomial F) :
    Polynomial (Polynomial F) :=
  (shiftX x₀ R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

def specializeZXShiftHom (x₀ z : F) :
    Polynomial (Polynomial F) →+* Polynomial F :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : F →+* Polynomial F).comp (Polynomial.evalRingHom z))
    (Polynomial.X + Polynomial.C x₀)

theorem specializeShiftX_eq (x₀ z : F) (R : TriPolynomial F) :
    specializeShiftX x₀ z R = R.map (specializeZXShiftHom x₀ z) := by
  unfold specializeShiftX shiftX specializeZXShiftHom shiftXCoefficient
  rw [Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

/-- Differentiate in the outer root variable and then set `X=x₀`, retaining
the seed variable `Z`. -/
def derivativeAtX (x₀ : F) (R : TriPolynomial F) :
    Polynomial (Polynomial F) :=
  R.derivative.map (Polynomial.evalRingHom (Polynomial.C x₀))

def translatePolynomial (x₀ : F) (p : Polynomial F) : Polynomial F :=
  Polynomial.eval₂ Polynomial.C (Polynomial.X + Polynomial.C x₀) p

@[simp] theorem translatePolynomial_coeff_zero (x₀ : F) (p : Polynomial F) :
    (translatePolynomial x₀ p).coeff 0 = p.eval x₀ := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold translatePolynomial
  change (Polynomial.evalRingHom 0)
      (Polynomial.eval₂ Polynomial.C (Polynomial.X + Polynomial.C x₀) p) = _
  rw [Polynomial.hom_eval₂]
  rw [show (Polynomial.evalRingHom 0).comp
      (Polynomial.C : F →+* Polynomial F) = RingHom.id F by
    ext a
    simp]
  simpa using (Polynomial.eval₂_id (p := p) (x := x₀))

theorem translatePolynomial_eval_sub (x₀ x : F) (p : Polynomial F) :
    (translatePolynomial x₀ p).eval (x - x₀) = p.eval x := by
  unfold translatePolynomial
  change (Polynomial.evalRingHom (x - x₀))
      (Polynomial.eval₂ Polynomial.C (Polynomial.X + Polynomial.C x₀) p) = _
  rw [Polynomial.hom_eval₂]
  rw [show (Polynomial.evalRingHom (x - x₀)).comp
      (Polynomial.C : F →+* Polynomial F) = RingHom.id F by
    ext a
    simp]
  rw [Polynomial.eval₂_id]
  congr 1
  simp

theorem translatePolynomial_natDegree_le (x₀ : F) (p : Polynomial F) :
    (translatePolynomial x₀ p).natDegree ≤ p.natDegree := by
  change (p.comp (Polynomial.X + Polynomial.C x₀)).natDegree ≤ p.natDegree
  exact Polynomial.natDegree_comp_le.trans (by simp)

/-- The elementary integral scaling preserves a polynomial root after
specialization and translation.  This is the root identity used by the scalar
Taylor recurrence, with `g=W(z)p`. -/
theorem specializeShiftX_integralScale_root (W : Polynomial F)
    (R : TriPolynomial F) (x₀ z : F) (p : Polynomial F)
    (hroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) p
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) = 0) :
    Polynomial.eval₂ (RingHom.id (Polynomial F))
        (translatePolynomial x₀ (Polynomial.C (W.eval z) * p))
        (specializeShiftX x₀ z
          (integralScale (Polynomial.C W) R)) = 0 := by
  let f : Polynomial (Polynomial F) →+* Polynomial F :=
    Polynomial.mapRingHom (Polynomial.evalRingHom z)
  have hy0 : Polynomial.eval₂ f p R = 0 := by
    simpa [Polynomial.eval₂_map, f] using hroot
  have hs := integralScale_root f (Polynomial.C W) R p hy0
  have hscaled :
      Polynomial.eval₂ (RingHom.id (Polynomial F))
        (Polynomial.C (W.eval z) * p)
        ((integralScale (Polynomial.C W) R).map f) = 0 := by
    simpa [f, Polynomial.eval₂_map] using hs
  let τ : Polynomial F →+* Polynomial F :=
    Polynomial.eval₂RingHom Polynomial.C
      (Polynomial.X + Polynomial.C x₀)
  have hm := congrArg τ hscaled
  rw [map_zero] at hm
  rw [Polynomial.hom_eval₂] at hm
  have hspec : specializeZXShiftHom x₀ z = τ.comp f := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [specializeZXShiftHom, τ, f]
    · simp [specializeZXShiftHom, τ, f]
  rw [specializeShiftX_eq]
  rw [hspec, ← Polynomial.map_map]
  change Polynomial.eval₂ (RingHom.id (Polynomial F))
      (τ (Polynomial.C (W.eval z) * p))
      (((integralScale (Polynomial.C W) R).map f).map τ) = 0
  rw [Polynomial.eval₂_map]
  simpa [τ, translatePolynomial, f] using hm

theorem constantCoeff_specializeShiftX_derivative
    (x₀ z y : F) (R : TriPolynomial F) (Γ : Polynomial F)
    (hΓ0 : Γ.coeff 0 = y) :
    (Polynomial.eval₂ (RingHom.id (Polynomial F)) Γ
      (specializeShiftX x₀ z R).derivative).coeff 0 =
      (specializeZ z (derivativeAtX x₀ R)).eval y := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom 0)
      (Polynomial.eval₂ (RingHom.id (Polynomial F)) Γ
        (specializeShiftX x₀ z R).derivative) = _
  rw [Polynomial.hom_eval₂]
  have hΓeval : Γ.eval 0 = y := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hΓ0]
  let L : Polynomial (Polynomial F) →+* F :=
    (Polynomial.evalRingHom 0).comp
      (specializeZXShiftHom x₀ z)
  let K : Polynomial (Polynomial F) →+* F :=
    (Polynomial.evalRingHom z).comp
      (Polynomial.evalRingHom (Polynomial.C x₀))
  have hLK : L = K := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [L, K, specializeZXShiftHom]
    · simp [L, K, specializeZXShiftHom]
  have hLK' : (Polynomial.evalRingHom 0).comp
      (specializeZXShiftHom x₀ z) =
      (Polynomial.evalRingHom z).comp
        (Polynomial.evalRingHom (Polynomial.C x₀)) := by
    simpa [L, K] using hLK
  rw [RingHom.comp_id]
  rw [show (Polynomial.evalRingHom 0) Γ = y by exact hΓeval]
  simp [specializeShiftX_eq, specializeZXShiftHom, derivativeAtX,
    specializeZ, Polynomial.derivative_map, Polynomial.eval_map,
    Polynomial.eval₂_map]
  change Polynomial.eval₂
      ((Polynomial.evalRingHom 0).comp (specializeZXShiftHom x₀ z)) y
        R.derivative =
    Polynomial.eval₂
      ((Polynomial.evalRingHom z).comp
        (Polynomial.evalRingHom (Polynomial.C x₀))) y R.derivative
  rw [hLK']

/-- Embed `F[Z][S]` into `(F[Z][T])[S]`, leaving `S` as the outer variable. -/
def embedShiftCoefficients :
    Polynomial (Polynomial F) →+* Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.mapRingHom Polynomial.C

/-- The finite polynomial `A₀ + A₁S + ... + AₜSᵗ`, where every `Aᵢ` is
represented in the basis `1,T,...,T^(h-1)`. -/
def historyPolynomial (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial (Polynomial (Polynomial F)) :=
  ∑ i : Fin (t + 1),
    Polynomial.monomial i.1 (vectorPolynomial h (history i))

/-- The concrete nonlinear coefficient extractor: the coefficient of `S^m`
in `R(Z,x₀+S,A₀+A₁S+⋯+AₜSᵗ)`.  It is a polynomial in `T` over `F[Z]`.
No quotient or denominator is hidden in this definition. -/
def nonlinearTaylorCoefficient (x₀ : F) (R : TriPolynomial F)
    (h t m : Nat) (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial (Polynomial F) :=
  (Polynomial.eval₂ embedShiftCoefficients (historyPolynomial h t history)
    (shiftX x₀ R)).coeff m

/-- The residual forcing at step `t+1`, reduced to the standard basis modulo
the monic branch polynomial. -/
def rawTaylorForcing (x₀ : F) (R : TriPolynomial F)
    (h : Nat) (Hbar : Polynomial (Polynomial F)) (t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Fin h → Polynomial F :=
  fun i => -((canonicalRemainder Hbar
    (nonlinearTaylorCoefficient x₀ R h t (t + 1) history)).coeff i.1)

theorem vectorPolynomial_rawTaylorForcing (x₀ : F) (R : TriPolynomial F)
    (h : Nat) (hh : 0 < h) (Hbar : Polynomial (Polynomial F))
    (hHbar : Hbar.Monic) (hHdeg : Hbar.natDegree = h) (t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    vectorPolynomial h (rawTaylorForcing x₀ R h Hbar t history) =
      -canonicalRemainder Hbar
        (nonlinearTaylorCoefficient x₀ R h t (t + 1) history) := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < h
  · let ii : Fin h := ⟨i, hi⟩
    rw [show i = ii.1 from rfl, coeff_vectorPolynomial]
    simp [rawTaylorForcing]
  · have hhi : h ≤ i := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h _ i hhi]
    rw [coeff_neg]
    have hdeg :
        (canonicalRemainder Hbar
          (nonlinearTaylorCoefficient x₀ R h t (t + 1) history)).degree < h := by
      have hHdegree : Hbar.degree = (h : WithBot Nat) := by
        rw [Hbar.degree_eq_natDegree hHbar.ne_zero, hHdeg]
      exact (canonicalRemainder_degree_lt hHbar _).trans_eq hHdegree
    have hz := (Polynomial.degree_lt_iff_coeff_zero _ _).mp hdeg i hhi
    rw [hz, neg_zero]

/-- Embed `F[Z][S]` into `(F[Z][T][U])[S]`.  The bookkeeping variable `U`
records the exponent of the determinant denominator in each Taylor monomial. -/
def embedShiftCoefficientsWithBookkeeping :
    Polynomial (Polynomial F) →+*
      Polynomial (Polynomial (Polynomial (Polynomial F))) :=
  Polynomial.mapRingHom
    ((Polynomial.C : Polynomial (Polynomial F) →+*
        Polynomial (Polynomial (Polynomial F))).comp
      (Polynomial.C : Polynomial F →+* Polynomial (Polynomial F)))

/-- Truncated Taylor history with `U^(2i-1)` attached to `Aᵢ`.  Evaluation at
`U=q⁻¹` therefore gives `Aᵢ/q^(2i-1)` (and attaches no denominator to `A₀`). -/
def denominatorBookHistory (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial (Polynomial (Polynomial (Polynomial F))) :=
  ∑ i : Fin (t + 1), Polynomial.monomial i.1
    (Polynomial.monomial (oddDenomExponent i.1)
      (vectorPolynomial h (history i)))

def bookDegreeBound (i : Nat) : Nat := if i = 0 then 0 else 2 * i - 1

def HasBookDegreeBound
    (P : Polynomial (Polynomial (Polynomial (Polynomial F)))) : Prop :=
  ∀ i, (P.coeff i).natDegree ≤ bookDegreeBound i

theorem bookDegreeBound_add (a b : Nat) :
    bookDegreeBound a + bookDegreeBound b ≤ bookDegreeBound (a + b) := by
  unfold bookDegreeBound
  split_ifs <;> omega

theorem HasBookDegreeBound.mul
    {P Q : Polynomial (Polynomial (Polynomial (Polynomial F)))}
    (hP : HasBookDegreeBound P) (hQ : HasBookDegreeBound Q) :
    HasBookDegreeBound (P * Q) := by
  intro m
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  have hm : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add (hP ij.1) (hQ ij.2)).trans
      (hm ▸ bookDegreeBound_add ij.1 ij.2))

theorem HasBookDegreeBound.one :
    HasBookDegreeBound
      (1 : Polynomial (Polynomial (Polynomial (Polynomial F)))) := by
  intro i
  by_cases hi : i = 0
  · subst i
    simp [bookDegreeBound]
  · rw [Polynomial.coeff_one, if_neg hi]
    simp

theorem HasBookDegreeBound.pow
    {P : Polynomial (Polynomial (Polynomial (Polynomial F)))}
    (hP : HasBookDegreeBound P) (j : Nat) : HasBookDegreeBound (P ^ j) := by
  induction j with
  | zero => simpa using (HasBookDegreeBound.one (F := F))
  | succ j ih => rw [pow_succ]; exact ih.mul hP

theorem denominatorBookHistory_hasBookDegreeBound (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    HasBookDegreeBound (denominatorBookHistory h t history) := by
  classical
  intro m
  simp only [denominatorBookHistory, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  split
  · rename_i him
    have hval : i.1 = m := by omega
    subst m
    exact (Polynomial.natDegree_monomial_le _).trans (by
      by_cases hi0 : i.1 = 0
      · simp [hi0, oddDenomExponent, bookDegreeBound]
      · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [hr]
        simp [oddDenomExponent, bookDegreeBound]
        omega)
  · simp

theorem denominatorBookHistory_natDegree_le (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    (denominatorBookHistory h t history).natDegree ≤ t := by
  classical
  unfold denominatorBookHistory
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem map_denominatorBookHistory {K : Type*} [Field K]
    (φ : Polynomial (Polynomial F) →+* K) (u : K) (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    (denominatorBookHistory h t history).map
        (Polynomial.eval₂RingHom φ u) =
      ∑ i : Fin (t + 1), Polynomial.monomial i.1
        (φ (vectorPolynomial h (history i)) *
          u ^ oddDenomExponent i.1) := by
  classical
  unfold denominatorBookHistory
  change (Polynomial.mapRingHom (Polynomial.eval₂RingHom φ u))
      (∑ i : Fin (t + 1), Polynomial.monomial i.1
        (Polynomial.monomial (oddDenomExponent i.1)
          (vectorPolynomial h (history i)))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change Polynomial.map (Polynomial.eval₂RingHom φ u)
      (Polynomial.monomial i.1
        (Polynomial.monomial (oddDenomExponent i.1)
          (vectorPolynomial h (history i)))) = _
  rw [Polynomial.map_monomial]
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

theorem map_denominatorBookHistory_eq_truncate {K : Type*} [Field K]
    (φ : Polynomial (Polynomial F) →+* K) (u : K) (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) (g : Polynomial K)
    (hhistory : ∀ i : Fin (t + 1),
      φ (vectorPolynomial h (history i)) *
          u ^ oddDenomExponent i.1 = g.coeff i.1) :
    (denominatorBookHistory h t history).map
        (Polynomial.eval₂RingHom φ u) = truncatePolynomial t g := by
  rw [map_denominatorBookHistory]
  unfold truncatePolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [hhistory i]

/-- Coefficient of `S^m` in the nonlinear substitution, retaining `U` as the
determinant-denominator bookkeeping variable. -/
def bookedNonlinearTaylorCoefficient (x₀ : F) (R : TriPolynomial F)
    (h t m : Nat) (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial (Polynomial (Polynomial F)) :=
  (Polynomial.eval₂ embedShiftCoefficientsWithBookkeeping
    (denominatorBookHistory h t history) (shiftX x₀ R)).coeff m

/-- Evaluating the bookkeeping variable commutes with the concrete nonlinear
coefficient extractor.  This is the exact connection between the universal
`F[Z][T]` numerator history and one scalar specialized Taylor history. -/
theorem eval₂_bookedNonlinearTaylorCoefficient {K : Type*} [Field K]
    (φ : Polynomial (Polynomial F) →+* K) (u : K) (x₀ : F)
    (R : TriPolynomial F) (h t m : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial.eval₂ φ u
        (bookedNonlinearTaylorCoefficient x₀ R h t m history) =
      (Polynomial.eval₂
        ((Polynomial.mapRingHom (Polynomial.eval₂RingHom φ u)).comp
          embedShiftCoefficientsWithBookkeeping)
        ((denominatorBookHistory h t history).map
          (Polynomial.eval₂RingHom φ u))
        (shiftX x₀ R)).coeff m := by
  unfold bookedNonlinearTaylorCoefficient
  change (Polynomial.eval₂RingHom φ u)
      ((Polynomial.eval₂ embedShiftCoefficientsWithBookkeeping
        (denominatorBookHistory h t history) (shiftX x₀ R)).coeff m) = _
  rw [← Polynomial.coeff_map]
  change ((Polynomial.mapRingHom (Polynomial.eval₂RingHom φ u))
      (Polynomial.eval₂ embedShiftCoefficientsWithBookkeeping
        (denominatorBookHistory h t history) (shiftX x₀ R))).coeff m = _
  rw [Polynomial.hom_eval₂]
  rw [Polynomial.coe_mapRingHom]

theorem map_evalZT_comp_embedShiftCoefficientsWithBookkeeping
    (z y u : F) :
    (Polynomial.mapRingHom
        (Polynomial.eval₂RingHom (evalZT z y) u)).comp
          embedShiftCoefficientsWithBookkeeping =
      Polynomial.mapRingHom (Polynomial.evalRingHom z) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [evalZT, embedShiftCoefficientsWithBookkeeping]
  · simp [evalZT, embedShiftCoefficientsWithBookkeeping]

/-- Fully scalar reading of a booked nonlinear coefficient.  After setting
`Z=z`, quotient variable `T=y`, and bookkeeping variable `U=u`, it is exactly
the coefficient obtained by substituting the corresponding scalar history
into the specialized shifted equation. -/
theorem eval_bookedNonlinearTaylorCoefficient (z y u x₀ : F)
    (R : TriPolynomial F) (h t m : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial.eval₂ (evalZT z y) u
        (bookedNonlinearTaylorCoefficient x₀ R h t m history) =
      (Polynomial.eval₂ (RingHom.id (Polynomial F))
        ((denominatorBookHistory h t history).map
          (Polynomial.eval₂RingHom (evalZT z y) u))
        (specializeShiftX x₀ z R)).coeff m := by
  rw [eval₂_bookedNonlinearTaylorCoefficient]
  rw [map_evalZT_comp_embedShiftCoefficientsWithBookkeeping]
  simp [specializeShiftX, Polynomial.eval₂_map]

theorem coeff_pow_top_bookDegree_le
    (P : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (hP : HasBookDegreeBound P) (s j : Nat) (hsupp : P.natDegree ≤ s) :
    ((P ^ j).coeff (s + 1)).natDegree ≤ 2 * s := by
  classical
  induction j with
  | zero =>
      rw [pow_zero, Polynomial.coeff_one, if_neg (by omega)]
      simp
  | succ j ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      apply Polynomial.natDegree_sum_le_of_forall_le
      rintro ⟨a, b⟩ hab
      have habsum : a + b = s + 1 := Finset.mem_antidiagonal.mp hab
      by_cases hb0 : b = 0
      · subst b
        simp only [add_zero] at habsum
        subst a
        have hP0 : (P.coeff 0).natDegree ≤ 0 := by
          simpa [bookDegreeBound] using hP 0
        exact Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add ih hP0)
      by_cases hbtop : b = s + 1
      · subst b
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (hsupp.trans_lt (Nat.lt_succ_self s)), mul_zero]
        simp
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
        have hblt : b < s + 1 := by omega
        have hapos : 0 < a := by omega
        exact Polynomial.natDegree_mul_le.trans
          ((Nat.add_le_add ((hP.pow j) a) (hP b)).trans (by
            simp [bookDegreeBound, Nat.ne_of_gt hapos, Nat.ne_of_gt hbpos]
            omega))

theorem bookedNonlinearTaylorCoefficient_natDegree_le (x₀ : F)
    (R : TriPolynomial F) (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history).natDegree ≤
      2 * t := by
  classical
  let G := denominatorBookHistory h t history
  have hGbook : HasBookDegreeBound G :=
    denominatorBookHistory_hasBookDegreeBound h t history
  have hGsupp : G.natDegree ≤ t :=
    denominatorBookHistory_natDegree_le h t history
  unfold bookedNonlinearTaylorCoefficient
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  rintro ⟨a, b⟩ hab
  have habsum : a + b = t + 1 := Finset.mem_antidiagonal.mp hab
  have hleft :
      ((embedShiftCoefficientsWithBookkeeping
        ((shiftX x₀ R).coeff j)).coeff a).natDegree ≤ 0 := by
    simp [embedShiftCoefficientsWithBookkeeping]
  have hright : ((G ^ j).coeff b).natDegree ≤ 2 * t := by
    by_cases hbtop : b = t + 1
    · subst b
      exact coeff_pow_top_bookDegree_le G hGbook t j hGsupp
    · have hble : b ≤ t := by omega
      exact ((hGbook.pow j) b).trans (by
        unfold bookDegreeBound
        split_ifs <;> omega)
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add hleft hright).trans (by omega))

/-- Replace a bookkeeping monomial `a U^e` by `q^(E-e) a`.  When the input has
`U`-degree at most `E`, this is exactly `q^E P(q⁻¹)` but stays in `F[Z][T]`. -/
def clearBookkeepingDenominator (q : Polynomial F) (E : Nat)
    (P : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial F) :=
  P.sum fun e a => Polynomial.C (q ^ (E - e)) * a

/-- Semantic correctness of denominator bookkeeping. -/
theorem map_clearBookkeepingDenominator {K : Type*} [Field K]
    (φ : Polynomial (Polynomial F) →+* K) (q : Polynomial F) (E : Nat)
    (P : Polynomial (Polynomial (Polynomial F)))
    (hdeg : P.natDegree ≤ E)
    (hq : φ (Polynomial.C q) ≠ 0) :
    φ (clearBookkeepingDenominator q E P) =
      φ (Polynomial.C q) ^ E *
        Polynomial.eval₂ φ (φ (Polynomial.C q))⁻¹ P := by
  classical
  rw [Polynomial.eval₂_eq_sum]
  unfold clearBookkeepingDenominator
  simp only [Polynomial.sum_def, map_sum, map_mul, map_pow, Polynomial.map_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have heP : e ≤ E :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp he)).trans hdeg
  have hsplit : E = (E - e) + e := by omega
  have hpow : φ (Polynomial.C q) ^ E =
      φ (Polynomial.C q) ^ (E - e) * φ (Polynomial.C q) ^ e := by
    calc
      φ (Polynomial.C q) ^ E =
          φ (Polynomial.C q) ^ ((E - e) + e) :=
        congrArg (fun n : Nat => φ (Polynomial.C q) ^ n) hsplit
      _ = _ := pow_add _ _ _
  have hcancel : φ (Polynomial.C q) ^ e *
      (φ (Polynomial.C q))⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  calc
    φ (Polynomial.C q) ^ (E - e) * φ (P.coeff e) =
        (φ (Polynomial.C q) ^ (E - e) * φ (P.coeff e)) *
          (φ (Polynomial.C q) ^ e *
            (φ (Polynomial.C q))⁻¹ ^ e) := by rw [hcancel, mul_one]
    _ = (φ (Polynomial.C q) ^ (E - e) * φ (Polynomial.C q) ^ e) *
          (φ (P.coeff e) * (φ (Polynomial.C q))⁻¹ ^ e) := by ring
    _ = φ (Polynomial.C q) ^ E *
          (φ (P.coeff e) * (φ (Polynomial.C q))⁻¹ ^ e) := by
      rw [hpow]

def bookkeepingHeight (P : Polynomial (Polynomial (Polynomial F))) : Nat :=
  P.support.sup fun e => polyHeight (P.coeff e)

theorem bookkeepingHeight_le_iff
    {P : Polynomial (Polynomial (Polynomial F))} {D : Nat} :
    bookkeepingHeight P ≤ D ↔ ∀ e, polyHeight (P.coeff e) ≤ D := by
  constructor
  · intro h e
    by_cases he : P.coeff e = 0
    · simp [he]
    · exact (Finset.le_sup (f := fun j => polyHeight (P.coeff j))
        (Polynomial.mem_support_iff.mpr he)).trans h
  · intro h
    exact Finset.sup_le fun e _ => h e

@[simp] theorem bookkeepingHeight_zero :
    bookkeepingHeight (0 : Polynomial (Polynomial (Polynomial F))) = 0 := by
  simp [bookkeepingHeight]

@[simp] theorem bookkeepingHeight_one :
    bookkeepingHeight (1 : Polynomial (Polynomial (Polynomial F))) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [bookkeepingHeight_le_iff]
  intro e
  by_cases he : e = 0
  · subst e
    rw [Polynomial.coeff_one]
    simp only [if_pos]
    change polyHeight (1 : Polynomial (Polynomial F)) ≤ 0
    rw [show (1 : Polynomial (Polynomial F)) =
      Polynomial.C (1 : Polynomial F) by simp, polyHeight_C]
    simp
  · rw [Polynomial.coeff_one, if_neg he]
    simp

theorem bookkeepingHeight_add_le
    (P Q : Polynomial (Polynomial (Polynomial F))) :
    bookkeepingHeight (P + Q) ≤
      max (bookkeepingHeight P) (bookkeepingHeight Q) := by
  rw [bookkeepingHeight_le_iff]
  intro e
  rw [Polynomial.coeff_add]
  exact (polyHeight_add_le _ _).trans
    (max_le_max ((bookkeepingHeight_le_iff.mp le_rfl) e)
      ((bookkeepingHeight_le_iff.mp le_rfl) e))

theorem bookkeepingHeight_mul_le
    (P Q : Polynomial (Polynomial (Polynomial F))) :
    bookkeepingHeight (P * Q) ≤
      bookkeepingHeight P + bookkeepingHeight Q := by
  rw [bookkeepingHeight_le_iff]
  intro e
  rw [Polynomial.coeff_mul]
  rw [polyHeight_le_iff]
  intro i
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  exact (natDegree_coeff_le_height _ i).trans
    ((polyHeight_mul_le _ _).trans
      (Nat.add_le_add ((bookkeepingHeight_le_iff.mp le_rfl) ij.1)
        ((bookkeepingHeight_le_iff.mp le_rfl) ij.2)))

theorem bookkeepingHeight_finset_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial (Polynomial (Polynomial F))) (D : Nat)
    (hf : ∀ i ∈ s, bookkeepingHeight (f i) ≤ D) :
    bookkeepingHeight (∑ i ∈ s, f i) ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (bookkeepingHeight_add_le _ _).trans
        (max_le (hf a (Finset.mem_insert_self a s))
          (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

theorem bookkeepingHeight_monomial_le (e : Nat)
    (P : Polynomial (Polynomial F)) :
    bookkeepingHeight (Polynomial.monomial e P) ≤ polyHeight P := by
  rw [bookkeepingHeight_le_iff]
  intro r
  rw [Polynomial.coeff_monomial]
  split <;> simp

theorem polyHeight_vectorPolynomial_le (h : Nat)
    (v : Fin h → Polynomial F) :
    polyHeight (vectorPolynomial h v) ≤ vectorHeight v := by
  rw [polyHeight_le_iff]
  intro i
  by_cases hi : i < h
  · let ii : Fin h := ⟨i, hi⟩
    rw [show i = ii.1 from rfl, coeff_vectorPolynomial]
    exact natDegree_vector_entry_le_vectorHeight v ii
  · rw [coeff_vectorPolynomial_eq_zero_of_le h v i (by omega)]
    simp

theorem bookkeepingHeight_denominatorBookHistory_coeff_le
    (h t m : Nat) (history : Fin (t + 1) → Fin h → Polynomial F)
    (hm : m ≤ t) :
    bookkeepingHeight ((denominatorBookHistory h t history).coeff m) ≤
      vectorHeight (history ⟨m, by omega⟩) := by
  classical
  unfold denominatorBookHistory
  rw [Polynomial.finsetSum_coeff]
  apply bookkeepingHeight_finset_sum_le
  intro i hi
  rw [Polynomial.coeff_monomial]
  split
  · rename_i him
    have hieq : i = ⟨m, by omega⟩ := Fin.ext him
    rw [hieq]
    exact (bookkeepingHeight_monomial_le _ _).trans
      (polyHeight_vectorPolynomial_le h _)
  · simp

/-- `Z`-height with the bookkeeping exponent credited at the exact rate
`q.natDegree`.  This is the invariant for which substituting
`U := q⁻¹` and clearing denominators loses no factor depending on `t`. -/
def HasQBookHeight (q : Polynomial F) (D : Nat)
    (P : Polynomial (Polynomial (Polynomial F))) : Prop :=
  ∀ e, polyHeight (P.coeff e) ≤ D + e * q.natDegree

theorem HasQBookHeight.zero (q : Polynomial F) (D : Nat) :
    HasQBookHeight q D 0 := by
  intro e
  simp

theorem HasQBookHeight.add {q : Polynomial F} {D : Nat}
    {P Q : Polynomial (Polynomial (Polynomial F))}
    (hP : HasQBookHeight q D P) (hQ : HasQBookHeight q D Q) :
    HasQBookHeight q D (P + Q) := by
  intro e
  rw [Polynomial.coeff_add]
  exact (polyHeight_add_le _ _).trans (max_le (hP e) (hQ e))

theorem HasQBookHeight.mono {q : Polynomial F} {D D' : Nat}
    {P : Polynomial (Polynomial (Polynomial F))}
    (hP : HasQBookHeight q D P) (hDD' : D ≤ D') :
    HasQBookHeight q D' P := by
  intro e
  exact (hP e).trans (Nat.add_le_add_right hDD' _)

theorem HasQBookHeight.monomial (q : Polynomial F) (D e : Nat)
    (P : Polynomial (Polynomial F))
    (hP : polyHeight P ≤ D + e * q.natDegree) :
    HasQBookHeight q D (Polynomial.monomial e P) := by
  intro r
  rw [Polynomial.coeff_monomial]
  split
  · rename_i her
    subst r
    exact hP
  · simp

theorem HasQBookHeight.mul {q : Polynomial F} {D₁ D₂ : Nat}
    {P Q : Polynomial (Polynomial (Polynomial F))}
    (hP : HasQBookHeight q D₁ P) (hQ : HasQBookHeight q D₂ Q) :
    HasQBookHeight q (D₁ + D₂) (P * Q) := by
  intro e
  rw [Polynomial.coeff_mul, polyHeight_le_iff]
  intro i
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  rintro ⟨a, b⟩ hab
  simp only [Prod.fst, Prod.snd]
  have habsum : a + b = e := Finset.mem_antidiagonal.mp hab
  exact (natDegree_coeff_le_height _ i).trans
    ((polyHeight_mul_le _ _).trans ((Nat.add_le_add (hP a) (hQ b)).trans (by
      calc
        D₁ + a * q.natDegree + (D₂ + b * q.natDegree) =
            D₁ + D₂ + (a + b) * q.natDegree := by ring
        _ ≤ D₁ + D₂ + e * q.natDegree := by rw [habsum])))

theorem HasQBookHeight.finset_sum {ι : Type*} [DecidableEq ι]
    {q : Polynomial F} {D : Nat} (s : Finset ι)
    (f : ι → Polynomial (Polynomial (Polynomial F)))
    (hf : ∀ i ∈ s, HasQBookHeight q D (f i)) :
    HasQBookHeight q D (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasQBookHeight.zero q D
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem HasQBookHeight.denominatorBookHistory_coeff
    (q : Polynomial F) (D h t m : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hm : m ≤ t)
    (hhistory : vectorHeight (history ⟨m, by omega⟩) ≤
      D + oddDenomExponent m * q.natDegree) :
    HasQBookHeight q D ((denominatorBookHistory h t history).coeff m) := by
  classical
  unfold denominatorBookHistory
  rw [Polynomial.finsetSum_coeff]
  apply HasQBookHeight.finset_sum
  intro i hi
  rw [Polynomial.coeff_monomial]
  split
  · rename_i him
    have hieq : i = ⟨m, by omega⟩ := Fin.ext him
    rw [hieq]
    exact HasQBookHeight.monomial q D _ _
      ((polyHeight_vectorPolynomial_le h _).trans hhistory)
  · exact HasQBookHeight.zero q D

theorem HasQBookHeight.denominatorBookHistory_coeff_zero
    (q : Polynomial F) (A h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hhistory : vectorHeight (history ⟨0, by omega⟩) ≤ A) :
    HasQBookHeight q A ((denominatorBookHistory h t history).coeff 0) := by
  apply HasQBookHeight.denominatorBookHistory_coeff q A h t 0 history (by omega)
  simpa [oddDenomExponent] using hhistory

/-- Convert the shifted positive-history invariant to the exact `q`-weighted
budget.  The identity behind the proof is
`(B-qdeg)+(r-1)(S-2qdeg)+(2r-1)qdeg = B+(r-1)S`. -/
theorem HasQBookHeight.denominatorBookHistory_coeff_pos
    (q : Polynomial F) (B S h t r : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hr : 0 < r) (hrt : r ≤ t)
    (hqB : q.natDegree ≤ B) (hqS : 2 * q.natDegree ≤ S)
    (hhistory : vectorHeight (history ⟨r, by omega⟩) ≤
      B + (r - 1) * S) :
    HasQBookHeight q
      ((B - q.natDegree) + (r - 1) * (S - 2 * q.natDegree))
      ((denominatorBookHistory h t history).coeff r) := by
  apply HasQBookHeight.denominatorBookHistory_coeff q
    ((B - q.natDegree) + (r - 1) * (S - 2 * q.natDegree))
    h t r history hrt
  refine hhistory.trans ?_
  rw [oddDenomExponent_eq r hr]
  have hB : B - q.natDegree + q.natDegree = B :=
    Nat.sub_add_cancel hqB
  have hS : S - 2 * q.natDegree + 2 * q.natDegree = S :=
    Nat.sub_add_cancel hqS
  have hrid : 2 * r - 1 = 1 + 2 * (r - 1) := by omega
  rw [hrid]
  have heq :
      (B - q.natDegree) + (r - 1) * (S - 2 * q.natDegree) +
          (1 + 2 * (r - 1)) * q.natDegree =
        B + (r - 1) * S := by
    calc
      (B - q.natDegree) + (r - 1) * (S - 2 * q.natDegree) +
            (1 + 2 * (r - 1)) * q.natDegree =
          (B - q.natDegree + q.natDegree) +
            (r - 1) * ((S - 2 * q.natDegree) + 2 * q.natDegree) := by ring
      _ = B + (r - 1) * S := by rw [hB, hS]
  exact heq.ge

/-- A shifted relation coefficient has bookkeeping degree zero.  Thus an
ordinary `Z`-height bound is also a `q`-book height bound, uniformly in the
Taylor coefficient selected from it. -/
theorem HasQBookHeight.embedShiftCoefficientsWithBookkeeping_coeff
    (q : Polynomial F) (D a : Nat) (P : Polynomial (Polynomial F))
    (hP : polyHeight P ≤ D) :
    HasQBookHeight q D
      ((embedShiftCoefficientsWithBookkeeping P).coeff a) := by
  intro e
  rw [show embedShiftCoefficientsWithBookkeeping P =
    P.map ((Polynomial.C : Polynomial (Polynomial F) →+*
      Polynomial (Polynomial (Polynomial F))).comp
        (Polynomial.C : Polynomial F →+* Polynomial (Polynomial F))) by rfl,
    Polynomial.coeff_map]
  change polyHeight ((Polynomial.C (Polynomial.C (P.coeff a))).coeff e) ≤
    D + e * q.natDegree
  rw [Polynomial.coeff_C]
  split
  · subst e
    rw [polyHeight_C]
    simpa using (natDegree_coeff_le_height P a).trans hP
  · simp

theorem HasQBookHeight.coeff_pow_zero
    (q : Polynomial F)
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A j : Nat) (hG0 : HasQBookHeight q A (G.coeff 0)) :
    HasQBookHeight q (j * A) ((G ^ j).coeff 0) := by
  induction j with
  | zero =>
      simpa [Polynomial.coeff_one] using
        (show HasQBookHeight q 0 (1 : Polynomial (Polynomial (Polynomial F))) by
          intro e
          by_cases he : e = 0
          · subst e
            rw [Polynomial.coeff_one]
            simp only [if_pos, Nat.zero_mul, Nat.add_zero]
            change polyHeight (1 : Polynomial (Polynomial F)) ≤ 0
            rw [show (1 : Polynomial (Polynomial F)) =
              Polynomial.C (1 : Polynomial F) by simp, polyHeight_C]
            simp
          · simp [Polynomial.coeff_one, he])
  | succ j ih =>
      rw [show Nat.succ j * A = j * A + A by exact Nat.succ_mul j A]
      rw [pow_succ, Polynomial.coeff_mul]
      apply HasQBookHeight.finset_sum
      rintro ⟨a, b⟩ hab
      simp only [Prod.fst, Prod.snd]
      have hab0 : a = 0 ∧ b = 0 := by
        have := Finset.mem_antidiagonal.mp hab
        omega
      rcases hab0 with ⟨rfl, rfl⟩
      exact ih.mul hG0

theorem HasQBookHeight.coeff_pow_pos
    (q : Polynomial F)
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A B L j m : Nat)
    (hG0 : HasQBookHeight q A (G.coeff 0))
    (hGpos : ∀ r, 0 < r →
      HasQBookHeight q (B + (r - 1) * L) (G.coeff r))
    (hBA : B ≤ A + L) (hm : 0 < m) :
    HasQBookHeight q (j * A + B + (m - 1) * L) ((G ^ j).coeff m) := by
  induction j generalizing m with
  | zero =>
      rw [pow_zero, Polynomial.coeff_one, if_neg (Nat.ne_of_gt hm)]
      exact HasQBookHeight.zero q _
  | succ j ih =>
      rw [show Nat.succ j * A = j * A + A by exact Nat.succ_mul j A]
      rw [pow_succ, Polynomial.coeff_mul]
      apply HasQBookHeight.finset_sum
      rintro ⟨a, b⟩ hab
      have habsum : a + b = m := Finset.mem_antidiagonal.mp hab
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst a
        simp only [zero_add] at habsum
        subst b
        exact ((HasQBookHeight.coeff_pow_zero q G A j hG0).mul
          (hGpos m hm)).mono (by omega)
      · rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · subst b
          simp only [add_zero] at habsum
          subst a
          exact ((ih m hm).mul hG0).mono (by omega)
        · have hleft := ih a hapos
          have hright := hGpos b hbpos
          have hsub : (a - 1) + (b - 1) = m - 2 := by omega
          have hstep : (m - 1) * L = (m - 2) * L + L := by
            have : m - 1 = (m - 2) + 1 := by omega
            rw [this, Nat.add_mul, Nat.one_mul]
          have hmul := hleft.mul hright
          intro e
          refine (hmul e).trans ?_
          calc
            (j * A + B + (a - 1) * L + (B + (b - 1) * L)) +
                e * q.natDegree =
              j * A + 2 * B + ((a - 1) + (b - 1)) * L +
                e * q.natDegree := by ring
            _ = j * A + 2 * B + (m - 2) * L + e * q.natDegree := by
              rw [hsub]
            _ ≤ j * A + A + B + (m - 1) * L + e * q.natDegree := by
              rw [hstep]
              omega

theorem HasQBookHeight.coeff_pow_top
    (q : Polynomial F)
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A B L s j : Nat)
    (hG0 : HasQBookHeight q A (G.coeff 0))
    (hGpos : ∀ r, 0 < r →
      HasQBookHeight q (B + (r - 1) * L) (G.coeff r))
    (hBA : B ≤ A + L) (hGsupp : G.natDegree ≤ s) :
    HasQBookHeight q (j * A + 2 * B + (s - 1) * L)
      ((G ^ j).coeff (s + 1)) := by
  induction j with
  | zero =>
      rw [pow_zero, Polynomial.coeff_one, if_neg (by omega)]
      exact HasQBookHeight.zero q _
  | succ j ih =>
      rw [show Nat.succ j * A = j * A + A by exact Nat.succ_mul j A]
      rw [pow_succ, Polynomial.coeff_mul]
      apply HasQBookHeight.finset_sum
      rintro ⟨a, b⟩ hab
      simp only [Prod.fst, Prod.snd]
      have habsum : a + b = s + 1 := Finset.mem_antidiagonal.mp hab
      by_cases hb0 : b = 0
      · subst b
        simp only [add_zero] at habsum
        subst a
        exact (ih.mul hG0).mono (by omega)
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
        by_cases hbtop : b = s + 1
        · subst b
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (hGsupp.trans_lt (Nat.lt_succ_self s)), mul_zero]
          exact HasQBookHeight.zero q _
        · have hapos : 0 < a := by omega
          have hleft := HasQBookHeight.coeff_pow_pos
            q G A B L j a hG0 hGpos hBA hapos
          have hright := hGpos b hbpos
          have hsub : (a - 1) + (b - 1) = s - 1 := by omega
          have hmul := hleft.mul hright
          intro e
          refine (hmul e).trans ?_
          calc
            (j * A + B + (a - 1) * L + (B + (b - 1) * L)) +
                e * q.natDegree =
              j * A + 2 * B + ((a - 1) + (b - 1)) * L +
                e * q.natDegree := by ring
            _ = j * A + 2 * B + (s - 1) * L + e * q.natDegree := by
              rw [hsub]
            _ ≤ j * A + A + 2 * B + (s - 1) * L +
                e * q.natDegree := by omega

/-- The first omitted Taylor coefficient of one summand in an `eval₂`.
The relation coefficient itself has bookkeeping degree zero; all denominator
weight is carried by the truncated history power. -/
theorem HasQBookHeight.coeff_embed_mul_pow_top
    (q : Polynomial F)
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (P : Polynomial (Polynomial F))
    (A B L Rheight s j : Nat)
    (hP : polyHeight P ≤ Rheight)
    (hG0 : HasQBookHeight q A (G.coeff 0))
    (hGpos : ∀ r, 0 < r →
      HasQBookHeight q (B + (r - 1) * L) (G.coeff r))
    (hBA : B ≤ A + L) (hGsupp : G.natDegree ≤ s) :
    HasQBookHeight q (j * A + 2 * B + Rheight + (s - 1) * L)
      ((embedShiftCoefficientsWithBookkeeping P * G ^ j).coeff (s + 1)) := by
  rw [Polynomial.coeff_mul]
  apply HasQBookHeight.finset_sum
  rintro ⟨a, b⟩ hab
  have habsum : a + b = s + 1 := Finset.mem_antidiagonal.mp hab
  have hleft := HasQBookHeight.embedShiftCoefficientsWithBookkeeping_coeff
    q Rheight a P hP
  by_cases hbtop : b = s + 1
  · subst b
    exact (hleft.mul (HasQBookHeight.coeff_pow_top
      q G A B L s j hG0 hGpos hBA hGsupp)).mono (by omega)
  · have hble : b ≤ s := by omega
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · exact (hleft.mul
        (HasQBookHeight.coeff_pow_zero q G A j hG0)).mono (by omega)
    · have hright := HasQBookHeight.coeff_pow_pos
        q G A B L j b hG0 hGpos hBA hbpos
      have hmul : (b - 1) * L ≤ (s - 1) * L :=
        Nat.mul_le_mul_right L (Nat.sub_le_sub_right hble 1)
      exact (hleft.mul hright).mono (by omega)

/-- Sharp `q`-book height of the first omitted coefficient of a nonlinear
substitution.  Its dependence on the outer relation degree is only through
`Ydeg * A`, while its dependence on the Taylor order is linear. -/
theorem HasQBookHeight.bookedNonlinearTaylorCoefficient_le
    (q : Polynomial F) (x₀ : F) (R : TriPolynomial F)
    (h t Ydeg A B L Rheight : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hRdeg : R.natDegree ≤ Ydeg)
    (hRheight : ∀ j, polyHeight ((shiftX x₀ R).coeff j) ≤ Rheight)
    (hG0 : HasQBookHeight q A
      ((denominatorBookHistory h t history).coeff 0))
    (hGpos : ∀ r, 0 < r →
      HasQBookHeight q (B + (r - 1) * L)
        ((denominatorBookHistory h t history).coeff r))
    (hBA : B ≤ A + L) :
    HasQBookHeight q
      (Ydeg * A + 2 * B + Rheight + (t - 1) * L)
      (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history) := by
  classical
  let G := denominatorBookHistory h t history
  have hGsupp : G.natDegree ≤ t :=
    denominatorBookHistory_natDegree_le h t history
  unfold bookedNonlinearTaylorCoefficient
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply HasQBookHeight.finset_sum
  intro j hj
  have hjR : j ≤ R.natDegree :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans Polynomial.natDegree_map_le
  have hjY : j ≤ Ydeg := hjR.trans hRdeg
  refine (HasQBookHeight.coeff_embed_mul_pow_top q G
    ((shiftX x₀ R).coeff j) A B L Rheight t j
    (hRheight j) hG0 hGpos hBA hGsupp).mono ?_
  have hjmul : j * A ≤ Ydeg * A := Nat.mul_le_mul_right A hjY
  omega

/-- At Taylor order zero the history is constant, so the coefficient of `S`
uses no positive history coefficient. -/
theorem HasQBookHeight.bookedNonlinearTaylorCoefficient_zero_le
    (q : Polynomial F) (x₀ : F) (R : TriPolynomial F)
    (h Ydeg A Rheight : Nat)
    (history : Fin 1 → Fin h → Polynomial F)
    (hRdeg : R.natDegree ≤ Ydeg)
    (hRheight : ∀ j, polyHeight ((shiftX x₀ R).coeff j) ≤ Rheight)
    (hG0 : HasQBookHeight q A
      ((denominatorBookHistory h 0 history).coeff 0)) :
    HasQBookHeight q (Ydeg * A + Rheight)
      (bookedNonlinearTaylorCoefficient x₀ R h 0 1 history) := by
  classical
  let G := denominatorBookHistory h 0 history
  have hGsupp : G.natDegree ≤ 0 :=
    denominatorBookHistory_natDegree_le h 0 history
  unfold bookedNonlinearTaylorCoefficient
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply HasQBookHeight.finset_sum
  intro j hj
  have hjR : j ≤ R.natDegree :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans Polynomial.natDegree_map_le
  have hjY : j ≤ Ydeg := hjR.trans hRdeg
  rw [Polynomial.coeff_mul]
  apply HasQBookHeight.finset_sum
  rintro ⟨a, b⟩ hab
  simp only [Prod.fst, Prod.snd]
  have habsum : a + b = 1 := Finset.mem_antidiagonal.mp hab
  have hleft := HasQBookHeight.embedShiftCoefficientsWithBookkeeping_coeff
    q Rheight a ((shiftX x₀ R).coeff j) (hRheight j)
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · have hright := HasQBookHeight.coeff_pow_zero q G A j hG0
    have hjmul : j * A ≤ Ydeg * A := Nat.mul_le_mul_right A hjY
    exact (hleft.mul hright).mono (by omega)
  · have hb1 : b = 1 := by omega
    subst b
    change HasQBookHeight q (Ydeg * A + Rheight)
      ((embedShiftCoefficientsWithBookkeeping
        ((shiftX x₀ R).coeff j)).coeff a * (G ^ j).coeff 1)
    have hpowdeg : (G ^ j).natDegree < 1 :=
      Polynomial.natDegree_pow_le.trans_lt (by
        have := Nat.mul_le_mul_left j hGsupp
        omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hpowdeg, mul_zero]
    exact HasQBookHeight.zero q _

/-- Uniform degree in the quotient variable `T`, coefficientwise in the
bookkeeping variable `U`. -/
def HasQuotientDegree (D : Nat)
    (P : Polynomial (Polynomial (Polynomial F))) : Prop :=
  ∀ e, (P.coeff e).natDegree ≤ D

theorem HasQuotientDegree.zero (D : Nat) :
    HasQuotientDegree (F := F) D 0 := by intro e; simp

theorem HasQuotientDegree.mono {D D' : Nat}
    {P : Polynomial (Polynomial (Polynomial F))}
    (hP : HasQuotientDegree D P) (hDD' : D ≤ D') :
    HasQuotientDegree D' P := fun e => (hP e).trans hDD'

theorem HasQuotientDegree.mul {D₁ D₂ : Nat}
    {P Q : Polynomial (Polynomial (Polynomial F))}
    (hP : HasQuotientDegree D₁ P) (hQ : HasQuotientDegree D₂ Q) :
    HasQuotientDegree (D₁ + D₂) (P * Q) := by
  intro e
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  rintro ⟨a, b⟩ hab
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP a) (hQ b))

theorem HasQuotientDegree.finset_sum {ι : Type*} [DecidableEq ι]
    {D : Nat} (s : Finset ι)
    (f : ι → Polynomial (Polynomial (Polynomial F)))
    (hf : ∀ i ∈ s, HasQuotientDegree D (f i)) :
    HasQuotientDegree D (∑ i ∈ s, f i) := by
  intro e
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact hf i hi e

theorem HasQuotientDegree.coeff_pow
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (D j m : Nat) (hG : ∀ r, HasQuotientDegree D (G.coeff r)) :
    HasQuotientDegree (j * D) ((G ^ j).coeff m) := by
  induction j generalizing m with
  | zero =>
      by_cases hm : m = 0
      · subst m
        rw [pow_zero, Polynomial.coeff_one, if_pos rfl]
        intro e
        by_cases he : e = 0
        · subst e
          rw [Polynomial.coeff_one, if_pos rfl]
          simp
        · rw [Polynomial.coeff_one, if_neg he]
          simp
      · rw [pow_zero, Polynomial.coeff_one, if_neg hm]
        exact HasQuotientDegree.zero _
  | succ j ih =>
      rw [Nat.succ_mul, pow_succ, Polynomial.coeff_mul]
      apply HasQuotientDegree.finset_sum
      rintro ⟨a, b⟩ hab
      exact HasQuotientDegree.mul (ih a) (hG b)

theorem vectorPolynomial_natDegree_le_pred (h : Nat) (hh : 0 < h)
    (v : Fin h → Polynomial F) :
    (vectorPolynomial h v).natDegree ≤ h - 1 := by
  by_cases hz : vectorPolynomial h v = 0
  · simp [hz]
  · have hlt : (vectorPolynomial h v).natDegree < h :=
      (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (vectorPolynomial_degree_lt h hh v)
    omega

theorem HasQuotientDegree.denominatorBookHistory_coeff
    (h t r : Nat) (hh : 0 < h)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    HasQuotientDegree (h - 1)
      ((denominatorBookHistory h t history).coeff r) := by
  classical
  unfold denominatorBookHistory
  rw [Polynomial.finsetSum_coeff]
  apply HasQuotientDegree.finset_sum
  intro i hi
  rw [Polynomial.coeff_monomial]
  split
  · intro e
    rw [Polynomial.coeff_monomial]
    split
    · exact vectorPolynomial_natDegree_le_pred h hh (history i)
    · simp
  · exact HasQuotientDegree.zero _

theorem HasQuotientDegree.bookedNonlinearTaylorCoefficient_le
    (x₀ : F) (R : TriPolynomial F) (h t Ydeg : Nat)
    (hh : 0 < h) (history : Fin (t + 1) → Fin h → Polynomial F)
    (hRdeg : R.natDegree ≤ Ydeg) :
    HasQuotientDegree (Ydeg * (h - 1))
      (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history) := by
  classical
  let G := denominatorBookHistory h t history
  have hG : ∀ r, HasQuotientDegree (h - 1) (G.coeff r) :=
    fun r => HasQuotientDegree.denominatorBookHistory_coeff h t r hh history
  unfold bookedNonlinearTaylorCoefficient
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply HasQuotientDegree.finset_sum
  intro j hj
  have hjR : j ≤ R.natDegree :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans Polynomial.natDegree_map_le
  have hjY : j ≤ Ydeg := hjR.trans hRdeg
  rw [Polynomial.coeff_mul]
  apply HasQuotientDegree.finset_sum
  rintro ⟨a, b⟩ hab
  have hleft : HasQuotientDegree (F := F) 0
      ((embedShiftCoefficientsWithBookkeeping
        ((shiftX x₀ R).coeff j)).coeff a) := by
    intro e
    rw [show embedShiftCoefficientsWithBookkeeping ((shiftX x₀ R).coeff j) =
      ((shiftX x₀ R).coeff j).map
        ((Polynomial.C : Polynomial (Polynomial F) →+*
          Polynomial (Polynomial (Polynomial F))).comp
          (Polynomial.C : Polynomial F →+* Polynomial (Polynomial F))) by rfl,
      Polynomial.coeff_map]
    change ((Polynomial.C (Polynomial.C
      (((shiftX x₀ R).coeff j).coeff a))).coeff e).natDegree ≤ 0
    rw [Polynomial.coeff_C]
    split <;> simp
  have hright := HasQuotientDegree.coeff_pow G (h - 1) j b hG
  have hjmul : j * (h - 1) ≤ Ydeg * (h - 1) :=
    Nat.mul_le_mul_right (h - 1) hjY
  exact (hleft.mul hright).mono (by omega)

theorem polyHeight_clearBookkeepingDenominator_le_of_qBook
    (q : Polynomial F) (E D : Nat)
    (P : Polynomial (Polynomial (Polynomial F)))
    (hdeg : P.natDegree ≤ E) (hP : HasQBookHeight q D P) :
    polyHeight (clearBookkeepingDenominator q E P) ≤
      D + E * q.natDegree := by
  classical
  rw [polyHeight_le_iff]
  intro i
  unfold clearBookkeepingDenominator
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  have heE : e ≤ E :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp he)).trans hdeg
  exact (natDegree_coeff_le_height _ i).trans
    ((polyHeight_mul_le _ _).trans (by
      rw [polyHeight_C]
      refine (Nat.add_le_add
        Polynomial.natDegree_pow_le
        (hP e)).trans ?_
      have hsplit : (E - e) * q.natDegree + e * q.natDegree =
          E * q.natDegree := by
        rw [← Nat.add_mul, Nat.sub_add_cancel heE]
      calc
        (E - e) * q.natDegree + (D + e * q.natDegree) =
            D + ((E - e) * q.natDegree + e * q.natDegree) := by ring
        _ ≤ D + E * q.natDegree := by rw [hsplit]))

theorem bookkeepingHeight_coeff_pow_zero_le
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A j : Nat) (hG0 : bookkeepingHeight (G.coeff 0) ≤ A) :
    bookkeepingHeight ((G ^ j).coeff 0) ≤ j * A := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      apply bookkeepingHeight_finset_sum_le
      rintro ⟨a, b⟩ hab
      simp only [Prod.fst, Prod.snd]
      have hab0 : a = 0 ∧ b = 0 := by
        have := Finset.mem_antidiagonal.mp hab
        omega
      rcases hab0 with ⟨rfl, rfl⟩
      exact (bookkeepingHeight_mul_le _ _).trans (by
        rw [Nat.succ_mul]
        exact Nat.add_le_add ih hG0)

/-- Weighted coefficient bound for a power of a truncated Taylor history.
Positive Taylor indices pay only their actual index, rather than `j` times
the largest history height. -/
theorem bookkeepingHeight_coeff_pow_pos_le
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A B L j m : Nat)
    (hG0 : bookkeepingHeight (G.coeff 0) ≤ A)
    (hGpos : ∀ r, 0 < r →
      bookkeepingHeight (G.coeff r) ≤ B + (r - 1) * L)
    (hBA : B ≤ A + L) (hm : 0 < m) :
    bookkeepingHeight ((G ^ j).coeff m) ≤
      j * A + B + (m - 1) * L := by
  induction j generalizing m with
  | zero => simp [Polynomial.coeff_one, Nat.ne_of_gt hm]
  | succ j ih =>
      rw [show Nat.succ j * A = j * A + A by exact Nat.succ_mul j A]
      rw [pow_succ, Polynomial.coeff_mul]
      apply bookkeepingHeight_finset_sum_le
      rintro ⟨a, b⟩ hab
      simp only [Prod.fst, Prod.snd]
      have habsum : a + b = m := Finset.mem_antidiagonal.mp hab
      refine (bookkeepingHeight_mul_le _ _).trans ?_
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst a
        simp only [zero_add] at habsum
        subst b
        have hleft := bookkeepingHeight_coeff_pow_zero_le G A j hG0
        have hright := hGpos m hm
        omega
      · rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · subst b
          simp only [add_zero] at habsum
          subst a
          have hleft := ih m hm
          omega
        · have hleft := ih a hapos
          have hright := hGpos b hbpos
          have hsub : (a - 1) + (b - 1) = m - 2 := by omega
          have hm2 : 2 ≤ m := by omega
          have hstep : (m - 1) * L = (m - 2) * L + L := by
            have : m - 1 = (m - 2) + 1 := by omega
            rw [this, Nat.add_mul, Nat.one_mul]
          calc
            bookkeepingHeight ((G ^ j).coeff a) +
                bookkeepingHeight (G.coeff b) ≤
                (j * A + B + (a - 1) * L) +
                  (B + (b - 1) * L) :=
              Nat.add_le_add hleft hright
            _ = j * A + 2 * B + ((a - 1) + (b - 1)) * L := by ring
            _ = j * A + 2 * B + (m - 2) * L := by rw [hsub]
            _ ≤ j * A + A + B + (m - 2) * L + L := by
              omega
            _ ≤ j * A + A + B + (m - 1) * L := by
              rw [hstep]
              omega

/-- At the first omitted Taylor coefficient `S^(s+1)`, truncation forces at
least two positive history factors.  This gains one full slope `L`. -/
theorem bookkeepingHeight_coeff_pow_top_le
    (G : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (A B L s j : Nat)
    (hG0 : bookkeepingHeight (G.coeff 0) ≤ A)
    (hGpos : ∀ r, 0 < r →
      bookkeepingHeight (G.coeff r) ≤ B + (r - 1) * L)
    (hBA : B ≤ A + L) (hGsupp : G.natDegree ≤ s) :
    bookkeepingHeight ((G ^ j).coeff (s + 1)) ≤
      j * A + 2 * B + (s - 1) * L := by
  induction j with
  | zero => simp [Polynomial.coeff_one]
  | succ j ih =>
      rw [show Nat.succ j * A = j * A + A by exact Nat.succ_mul j A]
      rw [pow_succ, Polynomial.coeff_mul]
      apply bookkeepingHeight_finset_sum_le
      rintro ⟨a, b⟩ hab
      simp only [Prod.fst, Prod.snd]
      have habsum : a + b = s + 1 := Finset.mem_antidiagonal.mp hab
      by_cases hb0 : b = 0
      · subst b
        simp only [add_zero] at habsum
        subst a
        refine (bookkeepingHeight_mul_le _ _).trans ?_
        calc
          bookkeepingHeight ((G ^ j).coeff (s + 1)) +
              bookkeepingHeight (G.coeff 0) ≤
              (j * A + 2 * B + (s - 1) * L) + A :=
            Nat.add_le_add ih hG0
          _ ≤ j * A + A + 2 * B + (s - 1) * L := by
            omega
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
        by_cases hbtop : b = s + 1
        · subst b
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (hGsupp.trans_lt (Nat.lt_succ_self s)), mul_zero,
            bookkeepingHeight_zero]
          simp
        · have hblt : b < s + 1 := by omega
          have hapos : 0 < a := by omega
          refine (bookkeepingHeight_mul_le _ _).trans ?_
          have hleft := bookkeepingHeight_coeff_pow_pos_le
            G A B L j a hG0 hGpos hBA hapos
          have hright := hGpos b hbpos
          have hsub : (a - 1) + (b - 1) = s - 1 := by omega
          calc
            bookkeepingHeight ((G ^ j).coeff a) +
                bookkeepingHeight (G.coeff b) ≤
                (j * A + B + (a - 1) * L) +
                  (B + (b - 1) * L) :=
              Nat.add_le_add hleft hright
            _ = j * A + 2 * B + ((a - 1) + (b - 1)) * L := by ring
            _ = j * A + 2 * B + (s - 1) * L := by rw [hsub]
            _ ≤ j * A + A + 2 * B + (s - 1) * L := by
              omega

theorem polyHeight_coeff_le_bookkeepingHeight
    (P : Polynomial (Polynomial (Polynomial F))) (e : Nat) :
    polyHeight (P.coeff e) ≤ bookkeepingHeight P := by
  by_cases he : P.coeff e = 0
  · simp [he]
  · exact Finset.le_sup (f := fun j => polyHeight (P.coeff j))
      (Polynomial.mem_support_iff.mpr he)

theorem polyHeight_clearBookkeepingDenominator_le (q : Polynomial F) (E : Nat)
    (P : Polynomial (Polynomial (Polynomial F))) :
    polyHeight (clearBookkeepingDenominator q E P) ≤
      E * q.natDegree + bookkeepingHeight P := by
  classical
  rw [polyHeight_le_iff]
  intro i
  unfold clearBookkeepingDenominator
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact (natDegree_coeff_le_height _ i).trans
    ((polyHeight_mul_le _ _).trans (by
      rw [polyHeight_C]
      exact Nat.add_le_add
        (Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_right q.natDegree (Nat.sub_le E e)))
        (polyHeight_coeff_le_bookkeepingHeight P e)))

/-- The integral, denominator-cleared nonlinear residual at positive step
`t+1`.  The sharp bookkeeping target is `E=2t`; the next adjugate solve adds
one more determinant, producing `q^(2t+1)`. -/
def clearedNonlinearTaylorCoefficient (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    Polynomial (Polynomial F) :=
  clearBookkeepingDenominator q (2 * t)
    (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history)

theorem clearedNonlinearTaylorCoefficient_natDegree_le
    (q : Polynomial F) (x₀ : F) (R : TriPolynomial F)
    (h t Ydeg : Nat) (hh : 0 < h)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hRdeg : R.natDegree ≤ Ydeg) :
    (clearedNonlinearTaylorCoefficient q x₀ R h t history).natDegree ≤
      Ydeg * (h - 1) := by
  classical
  have hbook := HasQuotientDegree.bookedNonlinearTaylorCoefficient_le
    x₀ R h t Ydeg hh history hRdeg
  unfold clearedNonlinearTaylorCoefficient clearBookkeepingDenominator
  rw [Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C]
    simpa using hbook e)

theorem map_clearedNonlinearTaylorCoefficient {K : Type*} [Field K]
    (φ : Polynomial (Polynomial F) →+* K) (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hq : φ (Polynomial.C q) ≠ 0) :
    φ (clearedNonlinearTaylorCoefficient q x₀ R h t history) =
      φ (Polynomial.C q) ^ (2 * t) *
        Polynomial.eval₂ φ (φ (Polynomial.C q))⁻¹
          (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history) := by
  exact map_clearBookkeepingDenominator φ q (2 * t) _
    (bookedNonlinearTaylorCoefficient_natDegree_le x₀ R h t history) hq

def clearedTaylorForcing (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h : Nat) (Hbar : Polynomial (Polynomial F))
    (t : Nat) (history : Fin (t + 1) → Fin h → Polynomial F) :
    Fin h → Polynomial F :=
  fun i => -((canonicalRemainder Hbar
    (clearedNonlinearTaylorCoefficient q x₀ R h t history)).coeff i.1)

theorem vectorPolynomial_clearedTaylorForcing (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    vectorPolynomial h (clearedTaylorForcing q x₀ R h Hbar t history) =
      -canonicalRemainder Hbar
        (clearedNonlinearTaylorCoefficient q x₀ R h t history) := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < h
  · let ii : Fin h := ⟨i, hi⟩
    rw [show i = ii.1 from rfl, coeff_vectorPolynomial]
    simp [clearedTaylorForcing]
  · have hhi : h ≤ i := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h _ i hhi, coeff_neg]
    have hdeg :
        (canonicalRemainder Hbar
          (clearedNonlinearTaylorCoefficient q x₀ R h t history)).degree < h := by
      have hHdegree : Hbar.degree = (h : WithBot Nat) := by
        rw [Hbar.degree_eq_natDegree hHbar.ne_zero, hHdeg]
      exact (canonicalRemainder_degree_lt hHbar _).trans_eq hHdegree
    have hz := (Polynomial.degree_lt_iff_coeff_zero _ _).mp hdeg i hhi
    rw [hz, neg_zero]

/-- The concrete scalar recurrence supplied by an actual polynomial root.
The entire lower-order history is present, and the denominator clearing is
proved by evaluation of the bookkeeping variable, rather than postulated as
an abstract `hsolve`. -/
theorem scalar_clearedTaylorForcing_equation
    (x₀ z y : F) (R : TriPolynomial F) (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (q : Polynomial F) (t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) (g : Polynomial F)
    (hy : (specializeZ z Hbar).eval y = 0)
    (hroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) g
      (specializeShiftX x₀ z R) = 0)
    (hg0 : g.coeff 0 = y) (hq : q.eval z ≠ 0)
    (hhistory : ∀ i : Fin (t + 1),
      evalZT z y (vectorPolynomial h (history i)) *
          (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1) :
    (specializeZ z (derivativeAtX x₀ R)).eval y *
        (q.eval z ^ (2 * t) * g.coeff (t + 1)) =
      evalZT z y
        (vectorPolynomial h
          (clearedTaylorForcing q x₀ R h Hbar t history)) := by
  let Γ := truncatePolynomial t g
  have hΓlow : ∀ i < t + 1, Γ.coeff i = g.coeff i := by
    intro i hi
    exact truncatePolynomial_coeff_of_lt t i g hi
  have hΓ0 : Γ.coeff 0 = y := by
    rw [hΓlow 0 (by omega), hg0]
  have htaylor := polynomial_root_taylor_coefficient_equation
    (t + 1) (by omega) (specializeShiftX x₀ z R) g Γ hroot hΓlow
      (truncatePolynomial_coeff_of_gt t (t + 1) g (by omega))
  rw [constantCoeff_specializeShiftX_derivative x₀ z y R Γ hΓ0] at htaylor
  have hbookHistory :
      (denominatorBookHistory h t history).map
          (Polynomial.eval₂RingHom (evalZT z y) (q.eval z)⁻¹) = Γ := by
    exact map_denominatorBookHistory_eq_truncate
      (evalZT z y) (q.eval z)⁻¹ h t history g hhistory
  have hbook := eval_bookedNonlinearTaylorCoefficient
    z y (q.eval z)⁻¹ x₀ R h t (t + 1) history
  rw [hbookHistory] at hbook
  have hclear := map_clearedNonlinearTaylorCoefficient
    (evalZT z y) q x₀ R h t history (by
      simpa [evalZT] using hq)
  have hqC : evalZT z y (Polynomial.C q) = q.eval z := by
    simp [evalZT]
  rw [hqC, hbook] at hclear
  have hforcing :
      evalZT z y
          (vectorPolynomial h
            (clearedTaylorForcing q x₀ R h Hbar t history)) =
        -evalZT z y
          (clearedNonlinearTaylorCoefficient q x₀ R h t history) := by
    rw [vectorPolynomial_clearedTaylorForcing q x₀ R h hh Hbar hHbar
      hHdeg t history]
    rw [map_neg]
    congr 1
    rw [evalZT_eq_specializeZ_eval, evalZT_eq_specializeZ_eval,
      eval_specializeZ_canonicalRemainder_at_root z y Hbar _ hy]
  rw [hforcing, hclear]
  calc
    (specializeZ z (derivativeAtX x₀ R)).eval y *
          (q.eval z ^ (2 * t) * g.coeff (t + 1)) =
        q.eval z ^ (2 * t) *
          ((specializeZ z (derivativeAtX x₀ R)).eval y *
            g.coeff (t + 1)) := by ring
    _ = q.eval z ^ (2 * t) *
          (-(Polynomial.eval₂ (RingHom.id (Polynomial F)) Γ
            (specializeShiftX x₀ z R)).coeff (t + 1)) := by rw [htaylor]
    _ = -(q.eval z ^ (2 * t) *
          (Polynomial.eval₂ (RingHom.id (Polynomial F)) Γ
            (specializeShiftX x₀ z R)).coeff (t + 1)) := by ring

def basisOneVector (h : Nat) : Fin h → Polynomial F :=
  fun i => if i.1 = 0 then 1 else 0

/-- Standard-basis representative of the quotient class of `T`. -/
def quotientVariableVector (h : Nat) (Hbar : Polynomial (Polynomial F)) :
    Fin h → Polynomial F :=
  fun i => (canonicalRemainder Hbar Polynomial.X).coeff i.1

theorem vectorPolynomial_quotientVariableVector (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) :
    vectorPolynomial h (quotientVariableVector h Hbar) =
      canonicalRemainder Hbar Polynomial.X := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < h
  · let ii : Fin h := ⟨i, hi⟩
    rw [show i = ii.1 from rfl, coeff_vectorPolynomial]
    rfl
  · have hhi : h ≤ i := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h _ i hhi]
    have hdeg : (canonicalRemainder Hbar Polynomial.X).degree < h := by
      have hHdegree : Hbar.degree = (h : WithBot Nat) := by
        rw [Hbar.degree_eq_natDegree hHbar.ne_zero, hHdeg]
      exact (canonicalRemainder_degree_lt hHbar _).trans_eq hHdegree
    exact ((Polynomial.degree_lt_iff_coeff_zero _ _).mp hdeg i hhi).symm

theorem eval_quotientVariableVector_at_root (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (z y : F)
    (hy : (specializeZ z Hbar).eval y = 0) :
    evalZT z y (vectorPolynomial h (quotientVariableVector h Hbar)) = y := by
  rw [vectorPolynomial_quotientVariableVector h hh Hbar hHbar hHdeg]
  rw [evalZT_eq_specializeZ_eval]
  change (specializeZ z (canonicalRemainder Hbar Polynomial.X)).eval y = y
  rw [eval_specializeZ_canonicalRemainder_at_root z y Hbar Polynomial.X hy]
  simp [specializeZ]

theorem vectorPolynomial_basisOneVector (h : Nat) (hh : 0 < h) :
    vectorPolynomial h (basisOneVector (F := F) h) = 1 := by
  classical
  apply Polynomial.ext
  intro n
  by_cases hn : n < h
  · let i : Fin h := ⟨n, hn⟩
    rw [show n = i.1 from rfl, coeff_vectorPolynomial]
    by_cases hn0 : n = 0
    · simp [basisOneVector, i, hn0]
    · simp [basisOneVector, i, hn0, Polynomial.coeff_one]
  · have hhn : h ≤ n := by omega
    rw [coeff_vectorPolynomial_eq_zero_of_le h _ n hhn]
    rw [Polynomial.coeff_one, if_neg (by omega)]

theorem vectorHeight_basisOneVector (h : Nat) :
    vectorHeight (basisOneVector (F := F) h) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [vectorHeight_le_iff]
  intro i
  by_cases hi : i.1 = 0 <;> simp [basisOneVector, hi]

theorem vectorHeight_clearedTaylorForcing_le (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (t : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F) :
    vectorHeight (clearedTaylorForcing q x₀ R h Hbar t history) ≤
      2 * t * q.natDegree +
        bookkeepingHeight
          (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history) +
        (clearedNonlinearTaylorCoefficient q x₀ R h t history).natDegree *
          polyHeight Hbar := by
  let P := clearedNonlinearTaylorCoefficient q x₀ R h t history
  let e := basisOneVector (F := F) h
  have hrepr := multiplicationMatrix_represents_mul_mod h hh Hbar hHbar hHdeg P e
  rw [vectorPolynomial_basisOneVector h hh, mul_one] at hrepr
  rw [vectorHeight_le_iff]
  intro i
  have hcoeff : (canonicalRemainder Hbar P).coeff i.1 =
      (multiplicationMatrix h Hbar P *ᵥ e) i := by
    rw [hrepr, coeff_vectorPolynomial]
  simp only [clearedTaylorForcing, P]
  rw [Polynomial.natDegree_neg, hcoeff]
  exact (natDegree_vector_entry_le_vectorHeight _ i).trans
    ((vectorHeight_mulVec_le (multiplicationMatrix h Hbar P) e).trans
      ((Nat.add_le_add (matrixHeight_multiplicationMatrix_le h Hbar P)
        (le_of_eq (vectorHeight_basisOneVector h))).trans (by
          have hPheight := polyHeight_clearBookkeepingDenominator_le q (2 * t)
            (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history)
          change polyHeight P + P.natDegree * polyHeight Hbar ≤ _
          exact Nat.add_le_add_right hPheight _)))

/-- Sharpened forcing-height estimate using exact `q`-book cancellation.
Compared with `vectorHeight_clearedTaylorForcing_le`, the Taylor-dependent
bookkeeping height is absorbed before the remainder calculation. -/
theorem vectorHeight_clearedTaylorForcing_le_of_qBook
    (q : Polynomial F) (x₀ : F)
    (R : TriPolynomial F) (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (t D Tdeg : Nat)
    (history : Fin (t + 1) → Fin h → Polynomial F)
    (hbook : HasQBookHeight q D
      (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history))
    (hTdeg : (clearedNonlinearTaylorCoefficient q x₀ R h t history).natDegree ≤
      Tdeg) :
    vectorHeight (clearedTaylorForcing q x₀ R h Hbar t history) ≤
      D + 2 * t * q.natDegree + Tdeg * polyHeight Hbar := by
  let P := clearedNonlinearTaylorCoefficient q x₀ R h t history
  let e := basisOneVector (F := F) h
  have hrepr := multiplicationMatrix_represents_mul_mod h hh Hbar hHbar hHdeg P e
  rw [vectorPolynomial_basisOneVector h hh, mul_one] at hrepr
  rw [vectorHeight_le_iff]
  intro i
  have hcoeff : (canonicalRemainder Hbar P).coeff i.1 =
      (multiplicationMatrix h Hbar P *ᵥ e) i := by
    rw [hrepr, coeff_vectorPolynomial]
  simp only [clearedTaylorForcing, P]
  rw [Polynomial.natDegree_neg, hcoeff]
  refine (natDegree_vector_entry_le_vectorHeight _ i).trans
    ((vectorHeight_mulVec_le (multiplicationMatrix h Hbar P) e).trans
      ((Nat.add_le_add (matrixHeight_multiplicationMatrix_le h Hbar P)
        (le_of_eq (vectorHeight_basisOneVector h))).trans ?_))
  have hPheight := polyHeight_clearBookkeepingDenominator_le_of_qBook
    q (2 * t) D
      (bookedNonlinearTaylorCoefficient x₀ R h t (t + 1) history)
      (bookedNonlinearTaylorCoefficient_natDegree_le x₀ R h t history) hbook
  change polyHeight P + P.natDegree * polyHeight Hbar ≤
    D + 2 * t * q.natDegree + Tdeg * polyHeight Hbar
  exact Nat.add_le_add hPheight (Nat.mul_le_mul_right (polyHeight Hbar) hTdeg)

/-- The course-of-values recursion step used by `finiteTaylorNumerators`. -/
def finiteTaylorNumeratorStep {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F)
    (t : Nat) (previous : (m : Nat) → m < t → Fin n → Polynomial F) :
    Fin n → Polynomial F :=
  match t with
  | 0 => a0
  | s + 1 => cramerStep M (rhs s (fun i => previous i.1 i.2))

/-- Numerators obtained by repeatedly applying Cramer's rule to an integral
right-hand-side constructor.  At step `t+1`, `rhs t` receives the entire
history `A₀,...,Aₜ`; this is essential because Taylor forcing is nonlinear in
the lower coefficients. -/
def finiteTaylorNumerators {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F) :
    Nat → Fin n → Polynomial F :=
  Nat.strongRec (finiteTaylorNumeratorStep M a0 rhs)

@[simp] theorem finiteTaylorNumerators_zero {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F) :
    finiteTaylorNumerators M a0 rhs 0 = a0 := by
  simpa only [finiteTaylorNumerators, finiteTaylorNumeratorStep] using
    (Nat.strongRec_eq (finiteTaylorNumeratorStep M a0 rhs) 0)

@[simp] theorem finiteTaylorNumerators_succ {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F) (t : Nat) :
    finiteTaylorNumerators M a0 rhs (t + 1) =
      cramerStep M (rhs t (fun i => finiteTaylorNumerators M a0 rhs i.1)) := by
  simpa only [finiteTaylorNumerators, finiteTaylorNumeratorStep] using
    (Nat.strongRec_eq (finiteTaylorNumeratorStep M a0 rhs) (t + 1))

/-- A deliberately simple linear height invariant.  It tolerates a loose
per-step forcing constant, which is enough for the `2^57` counting budget. -/
theorem vectorHeight_finiteTaylorNumerators_le {n E C : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F)
    (hM : ∀ i j, (M i j).natDegree ≤ E)
    (hrhs : ∀ t history,
      (∀ i, vectorHeight (history i) ≤
        vectorHeight a0 + i.1 * (n * E + C)) →
      vectorHeight (rhs t history) ≤
        C + vectorHeight a0 + t * (n * E + C)) (t : Nat) :
    vectorHeight (finiteTaylorNumerators M a0 rhs t) ≤
      vectorHeight a0 + t * (n * E + C) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    cases t with
    | zero => simp
    | succ t =>
      rw [finiteTaylorNumerators_succ]
      have hhistory : ∀ i : Fin (t + 1),
          vectorHeight (finiteTaylorNumerators M a0 rhs i.1) ≤
            vectorHeight a0 + i.1 * (n * E + C) := by
        intro i
        exact ih i.1 i.2
      refine (vectorHeight_cramerStep_le M _ hM (hrhs t _ hhistory)).trans ?_
      exact Nat.le_of_eq (by ring)

set_option maxHeartbeats 1000000 in
/-- A sharper two-level recurrence invariant.  The initial vector and the
first positive numerator have separate budgets; this is the form needed for
nonlinear Taylor coefficients, where the first omitted coefficient contains
at least two positive history factors. -/
theorem vectorHeight_finiteTaylorNumerators_shifted_le
    {n E A B C L : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F)
    (hM : ∀ i j, (M i j).natDegree ≤ E)
    (ha0 : vectorHeight a0 ≤ A)
    (hrhs : ∀ t history,
      vectorHeight (history ⟨0, by omega⟩) ≤ A →
      (∀ i, 0 < i.1 → vectorHeight (history i) ≤
        B + (i.1 - 1) * L) →
      vectorHeight (rhs t history) ≤ C + t * L)
    (hfirst : n * E + C ≤ B) (t : Nat) :
    if t = 0 then
      vectorHeight (finiteTaylorNumerators M a0 rhs t) ≤ A
    else
      vectorHeight (finiteTaylorNumerators M a0 rhs t) ≤ B + (t - 1) * L := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    cases t with
    | zero => simpa using ha0
    | succ t =>
      simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
      rw [finiteTaylorNumerators_succ]
      have hzero : vectorHeight
          (finiteTaylorNumerators M a0 rhs 0) ≤ A := by
        simpa using ih 0 (by omega)
      have hpos : ∀ i : Fin (t + 1), 0 < i.1 →
          vectorHeight (finiteTaylorNumerators M a0 rhs i.1) ≤
            B + (i.1 - 1) * L := by
        intro i hi
        have hii := ih i.1 i.2
        simpa [Nat.ne_of_gt hi] using hii
      refine (vectorHeight_cramerStep_le M _ hM
        (hrhs t _ hzero hpos)).trans ?_
      have hbound : n * E + (C + t * L) ≤ B + t * L := by
        omega
      exact hbound

/-- The actual integral Taylor numerator sequence for a monic branch `Hbar`.
Its forcing is the concrete nonlinear substitution coefficient with determinant
denominators cleared by the bookkeeping variable. -/
def concreteTaylorNumerators (x₀ : F) (R : TriPolynomial F) (h : Nat)
    (Hbar J : Polynomial (Polynomial F)) (a0 : Fin h → Polynomial F) :
    Nat → Fin h → Polynomial F :=
  let M := multiplicationMatrix h Hbar J
  finiteTaylorNumerators M a0
    (clearedTaylorForcing M.det x₀ R h Hbar)

/-- The determinant occurring in the Cap72 Taylor recurrence has comfortably
small `Z`-degree.  This packages the final numerical substitution separately
from the structural height lemmas, so callers only have to establish the four
natural Cap72 bounds for `Hbar` and the translated derivative `J`. -/
theorem cap72_multiplicationMatrix_det_natDegree_le_400000
    (h : Nat) (Hbar J : Polynomial (Polynomial F))
    (hh : h ≤ 11) (hHheight : polyHeight Hbar ≤ 792)
    (hJdegree : J.natDegree ≤ 10) (hJheight : polyHeight J ≤ 864) :
    (multiplicationMatrix h Hbar J).det.natDegree ≤ 400000 := by
  refine (natDegree_det_multiplicationMatrix_le h Hbar J).trans ?_
  have hinner : polyHeight J + J.natDegree * polyHeight Hbar ≤
      864 + 10 * 792 := by
    exact Nat.add_le_add hJheight (Nat.mul_le_mul hJdegree hHheight)
  exact (Nat.mul_le_mul hh hinner).trans (by norm_num)

/-- The concrete Cap72 forcing bound, with all large constants discharged.
The only qualitative input not encoded in the weighted-height argument is the
small quotient-variable degree of the cleared nonlinear coefficient. -/
theorem cap72_clearedTaylorForcing_height_le
    (q : Polynomial F) (x₀ : F) (R : TriPolynomial F) (h : Nat)
    (Hbar : Polynomial (Polynomial F))
    (hh : 0 < h) (hHbar : Hbar.Monic) (hHdeg : Hbar.natDegree = h)
    (hHheight : polyHeight Hbar ≤ 792)
    (hqdeg : q.natDegree ≤ 400000)
    (hRdeg : R.natDegree ≤ 11)
    (hRheight : ∀ j, polyHeight ((shiftX x₀ R).coeff j) ≤ 864)
    (hTdegree : ∀ t history,
      (clearedNonlinearTaylorCoefficient q x₀ R h t history).natDegree ≤ 110)
    (t : Nat) (history : Fin (t + 1) → Fin h → Polynomial F)
    (hzero : vectorHeight (history ⟨0, by omega⟩) ≤ 1000)
    (hpos : ∀ i, 0 < i.1 → vectorHeight (history i) ≤
      70100000 + (i.1 - 1) * 72000000) :
    vectorHeight (clearedTaylorForcing q x₀ R h Hbar t history) ≤
      70000000 + t * 72000000 := by
  have hqB : q.natDegree ≤ 70100000 := hqdeg.trans (by norm_num)
  have hqS : 2 * q.natDegree ≤ 72000000 :=
    (Nat.mul_le_mul_left 2 hqdeg).trans (by norm_num)
  by_cases ht0 : t = 0
  · subst t
    have hG0 := HasQBookHeight.denominatorBookHistory_coeff_zero
      q 1000 h 0 history hzero
    have hbook := HasQBookHeight.bookedNonlinearTaylorCoefficient_zero_le
      q x₀ R h 11 1000 864 history hRdeg hRheight hG0
    refine (vectorHeight_clearedTaylorForcing_le_of_qBook
      q x₀ R h hh Hbar hHbar hHdeg 0 (11 * 1000 + 864) 110 history
      hbook (hTdegree 0 history)).trans ?_
    have hrem : 110 * polyHeight Hbar ≤ 110 * 792 :=
      Nat.mul_le_mul_left 110 hHheight
    norm_num at hrem ⊢
    omega
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    let Bq := 70100000 - q.natDegree
    let Lq := 72000000 - 2 * q.natDegree
    have hBA : Bq ≤ 1000 + Lq := by
      dsimp [Bq, Lq]
      omega
    have hG0 := HasQBookHeight.denominatorBookHistory_coeff_zero
      q 1000 h t history hzero
    have hGpos : ∀ r, 0 < r → HasQBookHeight q
        (Bq + (r - 1) * Lq)
        ((denominatorBookHistory h t history).coeff r) := by
      intro r hr
      by_cases hrt : r ≤ t
      · exact HasQBookHeight.denominatorBookHistory_coeff_pos
          q 70100000 72000000 h t r history hr hrt hqB hqS
          (hpos ⟨r, by omega⟩ hr)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          ((denominatorBookHistory_natDegree_le h t history).trans_lt
            (Nat.lt_of_not_ge hrt))]
        exact HasQBookHeight.zero q _
    have hbook := HasQBookHeight.bookedNonlinearTaylorCoefficient_le
      q x₀ R h t 11 1000 Bq Lq 864 history
      hRdeg hRheight hG0 hGpos hBA
    have hv := vectorHeight_clearedTaylorForcing_le_of_qBook
      q x₀ R h hh Hbar hHbar hHdeg t
      (11 * 1000 + 2 * Bq + 864 + (t - 1) * Lq) 110 history
      hbook (hTdegree t history)
    refine hv.trans ?_
    have hB : 70100000 - q.natDegree + q.natDegree = 70100000 :=
      Nat.sub_add_cancel hqB
    have hS : 72000000 - 2 * q.natDegree + 2 * q.natDegree = 72000000 :=
      Nat.sub_add_cancel hqS
    have ht : t = (t - 1) + 1 := by omega
    have hcancel :
        (11 * 1000 + 2 * Bq + 864 + (t - 1) * Lq) +
            2 * t * q.natDegree =
          11 * 1000 + 2 * 70100000 + 864 + (t - 1) * 72000000 := by
      dsimp [Bq, Lq]
      rw [ht]
      calc
        (11 * 1000 + 2 * (70100000 - q.natDegree) + 864 +
              (t - 1) * (72000000 - 2 * q.natDegree)) +
              2 * ((t - 1) + 1) * q.natDegree =
            11 * 1000 + 2 *
                ((70100000 - q.natDegree) + q.natDegree) + 864 +
              (t - 1) *
                ((72000000 - 2 * q.natDegree) + 2 * q.natDegree) := by ring
        _ = 11 * 1000 + 2 * 70100000 + 864 +
              (t - 1) * 72000000 := by rw [hB, hS]
    rw [hcancel]
    have hrem : 110 * polyHeight Hbar ≤ 110 * 792 :=
      Nat.mul_le_mul_left 110 hHheight
    have hstep : t * 72000000 = (t - 1) * 72000000 + 72000000 := by
      calc
        t * 72000000 = (t - 1 + 1) * 72000000 :=
          congrArg (fun n : Nat => n * 72000000) ht
        _ = (t - 1) * 72000000 + 72000000 := by
          rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Numerical endpoint for the sharp shifted recurrence.  Unlike the discarded
single-line invariant, this contract distinguishes the constant Taylor term
from positive terms and is therefore compatible with the two-positive-factor
gain in `HasQBookHeight.coeff_pow_top`. -/
theorem cap72_concreteTaylorNumerators_height_le_10pow13_of_shifted_forcing
    (x₀ : F) (R : TriPolynomial F) (h : Nat)
    (Hbar J : Polynomial (Polynomial F)) (a0 : Fin h → Polynomial F)
    (hh : h ≤ 11) (hHheight : polyHeight Hbar ≤ 792)
    (hJdegree : J.natDegree ≤ 10) (hJheight : polyHeight J ≤ 864)
    (ha0 : vectorHeight a0 ≤ 1000)
    (hforcing : ∀ t history,
      vectorHeight (history ⟨0, by omega⟩) ≤ 1000 →
      (∀ i, 0 < i.1 → vectorHeight (history i) ≤
        70100000 + (i.1 - 1) * 72000000) →
      vectorHeight
        (clearedTaylorForcing (multiplicationMatrix h Hbar J).det
          x₀ R h Hbar t history) ≤ 70000000 + t * 72000000)
    (i : Nat) (hi : i ≤ 131071) :
    vectorHeight (concreteTaylorNumerators x₀ R h Hbar J a0 i) ≤
      10000000000000 := by
  have hentry : ∀ r c,
      (multiplicationMatrix h Hbar J r c).natDegree ≤ 8784 := by
    intro r c
    exact (natDegree_entry_le_matrixHeight (multiplicationMatrix h Hbar J) r c).trans
      ((matrixHeight_multiplicationMatrix_le h Hbar J).trans (by
        exact (Nat.add_le_add hJheight
          (Nat.mul_le_mul hJdegree hHheight)).trans (by norm_num)))
  have hfirst : h * 8784 + 70000000 ≤ 70100000 := by
    exact (Nat.add_le_add_right (Nat.mul_le_mul_right 8784 hh) _).trans (by norm_num)
  have hs := vectorHeight_finiteTaylorNumerators_shifted_le
    (M := multiplicationMatrix h Hbar J) (a0 := a0)
    (rhs := clearedTaylorForcing (multiplicationMatrix h Hbar J).det
      x₀ R h Hbar) (A := 1000) (B := 70100000) (C := 70000000)
    (L := 72000000) hentry ha0 hforcing hfirst i
  change vectorHeight
      (concreteTaylorNumerators x₀ R h Hbar J a0 i) ≤ 10000000000000
  by_cases hi0 : i = 0
  · subst i
    change vectorHeight
      (finiteTaylorNumerators (multiplicationMatrix h Hbar J) a0
        (clearedTaylorForcing (multiplicationMatrix h Hbar J).det
          x₀ R h Hbar) 0) ≤ 10000000000000
    rw [finiteTaylorNumerators_zero]
    exact ha0.trans (by norm_num)
  · have hs' : vectorHeight
        (concreteTaylorNumerators x₀ R h Hbar J a0 i) ≤
          70100000 + (i - 1) * 72000000 := by
      simpa [concreteTaylorNumerators, hi0] using hs
    exact hs'.trans ((Nat.add_le_add_left
      (Nat.mul_le_mul_right 72000000 (Nat.sub_le_sub_right hi 1)) _).trans
        (by norm_num))

@[simp] theorem concreteTaylorNumerators_zero (x₀ : F) (R : TriPolynomial F)
    (h : Nat) (Hbar J : Polynomial (Polynomial F))
    (a0 : Fin h → Polynomial F) :
    concreteTaylorNumerators x₀ R h Hbar J a0 0 = a0 := by
  simp [concreteTaylorNumerators]

@[simp] theorem concreteTaylorNumerators_succ (x₀ : F) (R : TriPolynomial F)
    (h : Nat) (Hbar J : Polynomial (Polynomial F))
    (a0 : Fin h → Polynomial F) (t : Nat) :
    concreteTaylorNumerators x₀ R h Hbar J a0 (t + 1) =
      cramerStep (multiplicationMatrix h Hbar J)
        (clearedTaylorForcing (multiplicationMatrix h Hbar J).det
          x₀ R h Hbar t
          (fun i => concreteTaylorNumerators x₀ R h Hbar J a0 i.1)) := by
  simp [concreteTaylorNumerators]

/-- End-to-end scalar specialization of the universal finite Taylor
numerators.  At every order the evaluated numerator, divided by the exact odd
power of the determinant, equals the corresponding coefficient of the actual
root polynomial. -/
theorem concreteTaylorNumerators_eval_eq_root_coefficient
    (x₀ z y : F) (R : TriPolynomial F) (h : Nat) (hh : 0 < h)
    (Hbar : Polynomial (Polynomial F)) (hHbar : Hbar.Monic)
    (hHdeg : Hbar.natDegree = h) (g : Polynomial F)
    (hy : (specializeZ z Hbar).eval y = 0)
    (hroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) g
      (specializeShiftX x₀ z R) = 0)
    (hg0 : g.coeff 0 = y)
    (hq : (multiplicationMatrix h Hbar (derivativeAtX x₀ R)).det.eval z ≠ 0)
    (hJ : (specializeZ z (derivativeAtX x₀ R)).eval y ≠ 0)
    (t : Nat) :
    evalZT z y
        (vectorPolynomial h
          (concreteTaylorNumerators x₀ R h Hbar (derivativeAtX x₀ R)
            (quotientVariableVector h Hbar) t)) *
      ((multiplicationMatrix h Hbar (derivativeAtX x₀ R)).det.eval z)⁻¹ ^
        oddDenomExponent t = g.coeff t := by
  let q := (multiplicationMatrix h Hbar (derivativeAtX x₀ R)).det
  induction t using Nat.strongRecOn with
  | ind t ih =>
      cases t with
      | zero =>
          simp only [concreteTaylorNumerators_zero, oddDenomExponent,
            pow_zero, mul_one]
          rw [eval_quotientVariableVector_at_root h hh Hbar hHbar hHdeg z y hy,
            hg0]
      | succ s =>
          have hhistory : ∀ i : Fin (s + 1),
              evalZT z y
                  (vectorPolynomial h
                    (concreteTaylorNumerators x₀ R h Hbar
                      (derivativeAtX x₀ R) (quotientVariableVector h Hbar)
                      i.1)) *
                (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1 := by
            intro i
            simpa [q] using ih i.1 i.2
          have hsolve := scalar_clearedTaylorForcing_equation
            x₀ z y R h hh Hbar hHbar hHdeg q s
            (fun i => concreteTaylorNumerators x₀ R h Hbar
              (derivativeAtX x₀ R) (quotientVariableVector h Hbar) i.1)
            g hy hroot hg0 (by simpa [q] using hq) hhistory
          let b := clearedTaylorForcing q x₀ R h Hbar s
            (fun i => concreteTaylorNumerators x₀ R h Hbar
              (derivativeAtX x₀ R) (quotientVariableVector h Hbar) i.1)
          have hnext := scalar_cramerStep_specialization_unique_succ
            h hh Hbar hHbar hHdeg (derivativeAtX x₀ R) b z y
            (g.coeff (s + 1)) hy hq hJ s (by
              simpa [q, b, evalZT_eq_specializeZ_eval] using hsolve)
          rw [concreteTaylorNumerators_succ]
          simp only [oddDenomExponent]
          change evalZT z y
              (vectorPolynomial h
                (cramerStep
                  (multiplicationMatrix h Hbar (derivativeAtX x₀ R)) b)) *
                (q.eval z)⁻¹ ^ (2 * s + 1) = g.coeff (s + 1)
          rw [hnext]
          simp [q, evalZT_eq_specializeZ_eval, mul_comm]

/-- Specialized bridge for the actual nonmonic branch data.  Both the branch
equation and the ambient root equation are integralized before invoking the
finite Taylor recursion. -/
theorem integralizedTaylorNumerators_eval_eq_scaled_root_coefficient
    (x₀ z : F) (R : TriPolynomial F) (H : Polynomial (Polynomial F))
    (h : Nat) (hh : 0 < h) (hHdeg : H.natDegree = h)
    (p : Polynomial F)
    (hHroot : (specializeZ z H).eval (p.eval x₀) = 0)
    (hRroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) p
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) = 0)
    (hq : (multiplicationMatrix h (integralMonicize H)
      (derivativeAtX x₀
        (integralScale (Polynomial.C H.leadingCoeff) R))).det.eval z ≠ 0)
    (hJ : (specializeZ z (derivativeAtX x₀
      (integralScale (Polynomial.C H.leadingCoeff) R))).eval
        (H.leadingCoeff.eval z * p.eval x₀) ≠ 0)
    (t : Nat) :
    let Rbar := integralScale (Polynomial.C H.leadingCoeff) R
    let Hbar := integralMonicize H
    let J := derivativeAtX x₀ Rbar
    let g := translatePolynomial x₀
      (Polynomial.C (H.leadingCoeff.eval z) * p)
    evalZT z (H.leadingCoeff.eval z * p.eval x₀)
        (vectorPolynomial h
          (concreteTaylorNumerators x₀ Rbar h Hbar J
            (quotientVariableVector h Hbar) t)) *
      ((multiplicationMatrix h Hbar J).det.eval z)⁻¹ ^
        oddDenomExponent t = g.coeff t := by
  dsimp only
  let Rbar := integralScale (Polynomial.C H.leadingCoeff) R
  let Hbar := integralMonicize H
  let g := translatePolynomial x₀
    (Polynomial.C (H.leadingCoeff.eval z) * p)
  have hHbar : Hbar.Monic := integralMonicize_monic H
  have hHbarDeg : Hbar.natDegree = h := by
    rw [integralMonicize_natDegree, hHdeg]
  have hy : (specializeZ z Hbar).eval
      (H.leadingCoeff.eval z * p.eval x₀) = 0 := by
    exact integralMonicize_specialized_root H (hHdeg ▸ hh) z (p.eval x₀) hHroot
  have hg0 : g.coeff 0 = H.leadingCoeff.eval z * p.eval x₀ := by
    simp [g, translatePolynomial_coeff_zero]
  have hgroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) g
      (specializeShiftX x₀ z Rbar) = 0 := by
    exact specializeShiftX_integralScale_root H.leadingCoeff R x₀ z p hRroot
  exact concreteTaylorNumerators_eval_eq_root_coefficient x₀ z
    (H.leadingCoeff.eval z * p.eval x₀) Rbar h hh Hbar hHbar hHbarDeg g hy
    hgroot hg0 hq hJ t

/-- Put all Taylor coefficients through order `k` over the single common
denominator `q^(2k-1)`.  The result is still integral in `F[Z][T][S]`. -/
def commonDenominatorTaylorTruncation (h k : Nat) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) :
    Polynomial (Polynomial (Polynomial F)) :=
  ∑ i : Fin (k + 1), Polynomial.monomial i.1
    (Polynomial.C (q ^ (oddDenomExponent k - oddDenomExponent i.1)) *
      vectorPolynomial h (seq i.1))

theorem polyHeight_commonDenominatorTaylorTruncation_coeff_le
    (h k i : Nat) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F) :
    polyHeight ((commonDenominatorTaylorTruncation h k q seq).coeff i) ≤
      oddDenomExponent k * q.natDegree + vectorHeight (seq i) := by
  classical
  unfold commonDenominatorTaylorTruncation
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hi : i < k + 1
  · let ii : Fin (k + 1) := ⟨i, hi⟩
    rw [Finset.sum_eq_single ii]
    · simp only [ii, if_pos rfl]
      exact (polyHeight_mul_le _ _).trans (by
        rw [polyHeight_C]
        exact Nat.add_le_add
          (Polynomial.natDegree_pow_le.trans
            (Nat.mul_le_mul_right q.natDegree
              (Nat.sub_le (oddDenomExponent k) (oddDenomExponent i))))
          (polyHeight_vectorPolynomial_le h (seq i)))
    · intro b hb hbne
      rw [if_neg (by
        intro heq
        apply hbne
        exact Fin.ext heq)]
    · intro hmem
      exact absurd (Finset.mem_univ ii) hmem
  · have hii : ∀ j : Fin (k + 1), j.1 ≠ i := by
      intro j hji
      subst i
      omega
    simp only [if_neg (hii _), Finset.sum_const_zero]
    simp

theorem bookkeepingHeight_commonDenominatorTaylorTruncation_le
    (h k D : Nat) (q : Polynomial F)
    (seq : Nat → Fin h → Polynomial F)
    (hseq : ∀ i ≤ k, vectorHeight (seq i) ≤ D) :
    bookkeepingHeight (commonDenominatorTaylorTruncation h k q seq) ≤
      oddDenomExponent k * q.natDegree + D := by
  have hGdeg :
      (commonDenominatorTaylorTruncation h k q seq).natDegree ≤ k := by
    classical
    unfold commonDenominatorTaylorTruncation
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  unfold bookkeepingHeight
  apply Finset.sup_le
  intro i hi
  exact (polyHeight_commonDenominatorTaylorTruncation_coeff_le h k i q seq).trans
    (Nat.add_le_add_left (hseq i (by
      have := Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hi)
      exact this.trans hGdeg)) _)

theorem polyHeight_eval_scalar_le_bookkeepingHeight
    (P : Polynomial (Polynomial (Polynomial F))) (s : F) :
    polyHeight (P.eval (Polynomial.C (Polynomial.C s))) ≤
      bookkeepingHeight P := by
  classical
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def]
  induction P.support using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      refine (polyHeight_add_le _ _).trans (max_le ?_ ih)
      exact (polyHeight_mul_le _ _).trans (by
        have hcoeff := polyHeight_coeff_le_bookkeepingHeight P a
        rw [show polyHeight
          ((Polynomial.C (Polynomial.C s) : Polynomial (Polynomial F)) ^ a) = 0 by
            rw [show (Polynomial.C (Polynomial.C s) : Polynomial (Polynomial F)) ^ a =
              Polynomial.C ((Polynomial.C s : Polynomial F) ^ a) by rw [map_pow],
              polyHeight_C]
            simp, Nat.add_zero]
        exact hcoeff)

/-- Numerical height package used by the `2^47` rich-coordinate obstruction.
The constants deliberately leave more than a factor fifty before `2^47`
after the standard resultant estimate `11*height + 11*72`. -/
theorem commonDenominatorTaylorTruncation_height_lt_2pow47
    (h k : Nat) (q : Polynomial F) (seq : Nat → Fin h → Polynomial F)
    (hk : k ≤ 131071) (hqdeg : q.natDegree ≤ 400000)
    (hseq : ∀ i ≤ k, vectorHeight (seq i) ≤ 10000000000000) :
    bookkeepingHeight (commonDenominatorTaylorTruncation h k q seq) ≤
        10104857200000 ∧
      (∀ s : F, polyHeight
        ((commonDenominatorTaylorTruncation h k q seq).eval
          (Polynomial.C (Polynomial.C s))) ≤ 10104857200000) ∧
      11 * 10104857200000 + 11 * 72 < 2 ^ 47 := by
  have hodd : oddDenomExponent k ≤ 262143 := by
    cases k <;> simp [oddDenomExponent] at * <;> omega
  have hheight := bookkeepingHeight_commonDenominatorTaylorTruncation_le
    h k 10000000000000 q seq hseq
  have hnum : oddDenomExponent k * q.natDegree + 10000000000000 ≤
      10104857200000 := by
    exact (Nat.add_le_add_right (Nat.mul_le_mul hodd hqdeg) _).trans (by norm_num)
  have hmain := hheight.trans hnum
  refine ⟨hmain, ?_, by norm_num⟩
  intro s
  exact (polyHeight_eval_scalar_le_bookkeepingHeight _ s).trans hmain

theorem map_commonDenominatorTaylorTruncation
    (h k : Nat) (q : Polynomial F) (seq : Nat → Fin h → Polynomial F)
    (z y : F) (g : Polynomial F) (hq : q.eval z ≠ 0)
    (hseq : ∀ i : Fin (k + 1),
      evalZT z y (vectorPolynomial h (seq i.1)) *
          (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1) :
    (commonDenominatorTaylorTruncation h k q seq).map (evalZT z y) =
      Polynomial.C (q.eval z ^ oddDenomExponent k) *
        truncatePolynomial k g := by
  classical
  unfold commonDenominatorTaylorTruncation truncatePolynomial
  change (Polynomial.mapRingHom (evalZT z y))
      (∑ i : Fin (k + 1), Polynomial.monomial i.1
        (Polynomial.C (q ^ (oddDenomExponent k - oddDenomExponent i.1)) *
          vectorPolynomial h (seq i.1))) = _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change Polynomial.map (evalZT z y)
      (Polynomial.monomial i.1
        (Polynomial.C (q ^ (oddDenomExponent k - oddDenomExponent i.1)) *
          vectorPolynomial h (seq i.1))) = _
  rw [Polynomial.map_monomial, map_mul]
  rw [Polynomial.C_mul_monomial]
  rw [show evalZT z y
      (Polynomial.C (q ^ (oddDenomExponent k - oddDenomExponent i.1))) =
        q.eval z ^ (oddDenomExponent k - oddDenomExponent i.1) by
      rw [show Polynomial.C
        (q ^ (oddDenomExponent k - oddDenomExponent i.1)) =
          (Polynomial.C q : Polynomial (Polynomial F)) ^
            (oddDenomExponent k - oddDenomExponent i.1) by rw [map_pow],
        map_pow]
      simp [evalZT]]
  change Polynomial.monomial i.1
      (q.eval z ^ (oddDenomExponent k - oddDenomExponent i.1) *
        evalZT z y (vectorPolynomial h (seq i.1))) =
    Polynomial.monomial i.1
      (q.eval z ^ oddDenomExponent k * g.coeff i.1)
  congr 1
  let a := q.eval z
  let e := oddDenomExponent i.1
  let E := oddDenomExponent k
  let N := evalZT z y (vectorPolynomial h (seq i.1))
  have hei : e ≤ E := by
    simp only [e, E, oddDenomExponent]
    split <;> split <;> omega
  have hinv : a ^ e * a⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by simpa [a] using hq), one_pow]
  have hN : N = a ^ e * g.coeff i.1 := by
    calc
      N = (a ^ e * a⁻¹ ^ e) * N := by rw [hinv, one_mul]
      _ = a ^ e * (N * a⁻¹ ^ e) := by ring
      _ = a ^ e * g.coeff i.1 := by rw [hseq i]
  change a ^ (E - e) * N = a ^ E * g.coeff i.1
  rw [hN]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hei]

theorem eval_commonDenominatorTaylorTruncation
    (h k : Nat) (q : Polynomial F) (seq : Nat → Fin h → Polynomial F)
    (z y s : F) (g : Polynomial F) (hq : q.eval z ≠ 0)
    (hseq : ∀ i : Fin (k + 1),
      evalZT z y (vectorPolynomial h (seq i.1)) *
          (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1) :
    ((commonDenominatorTaylorTruncation h k q seq).map (evalZT z y)).eval s =
      q.eval z ^ oddDenomExponent k * (truncatePolynomial k g).eval s := by
  rw [map_commonDenominatorTaylorTruncation h k q seq z y g hq hseq]
  simp

/-- Concrete common-denominator evaluation promised by the extraction: at a
good seed/root and every point `x`, the universal truncation evaluates to
`q(z)^(2k-1) W(z) p_z(x)`. -/
theorem eval_integralized_commonTaylorTruncation
    (x₀ x z : F) (R : TriPolynomial F) (H : Polynomial (Polynomial F))
    (h k : Nat) (hh : 0 < h) (hHdeg : H.natDegree = h)
    (p : Polynomial F) (hpdeg : p.natDegree ≤ k)
    (hHroot : (specializeZ z H).eval (p.eval x₀) = 0)
    (hRroot : Polynomial.eval₂ (RingHom.id (Polynomial F)) p
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) = 0)
    (hq : (multiplicationMatrix h (integralMonicize H)
      (derivativeAtX x₀
        (integralScale (Polynomial.C H.leadingCoeff) R))).det.eval z ≠ 0)
    (hJ : (specializeZ z (derivativeAtX x₀
      (integralScale (Polynomial.C H.leadingCoeff) R))).eval
        (H.leadingCoeff.eval z * p.eval x₀) ≠ 0) :
    let Rbar := integralScale (Polynomial.C H.leadingCoeff) R
    let Hbar := integralMonicize H
    let J := derivativeAtX x₀ Rbar
    let q := (multiplicationMatrix h Hbar J).det
    let seq := concreteTaylorNumerators x₀ Rbar h Hbar J
      (quotientVariableVector h Hbar)
    ((commonDenominatorTaylorTruncation h k q seq).map
      (evalZT z (H.leadingCoeff.eval z * p.eval x₀))).eval (x - x₀) =
        q.eval z ^ oddDenomExponent k *
          (H.leadingCoeff.eval z * p.eval x) := by
  dsimp only
  let Rbar := integralScale (Polynomial.C H.leadingCoeff) R
  let Hbar := integralMonicize H
  let J := derivativeAtX x₀ Rbar
  let q := (multiplicationMatrix h Hbar J).det
  let seq := concreteTaylorNumerators x₀ Rbar h Hbar J
    (quotientVariableVector h Hbar)
  let g := translatePolynomial x₀
    (Polynomial.C (H.leadingCoeff.eval z) * p)
  have hseq : ∀ i : Fin (k + 1),
      evalZT z (H.leadingCoeff.eval z * p.eval x₀)
          (vectorPolynomial h (seq i.1)) *
        (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1 := by
    intro i
    exact integralizedTaylorNumerators_eval_eq_scaled_root_coefficient
      x₀ z R H h hh hHdeg p hHroot hRroot hq hJ i.1
  have hgdeg : g.natDegree ≤ k := by
    refine (translatePolynomial_natDegree_le x₀
      (Polynomial.C (H.leadingCoeff.eval z) * p)).trans ?_
    exact Polynomial.natDegree_mul_le.trans (by simpa using hpdeg)
  rw [eval_commonDenominatorTaylorTruncation h k q seq z
    (H.leadingCoeff.eval z * p.eval x₀) (x - x₀) g (by simpa [q] using hq)
    hseq]
  rw [truncatePolynomial_eq_self k g hgdeg]
  rw [show g.eval (x - x₀) = H.leadingCoeff.eval z * p.eval x by
    simp [g, translatePolynomial_eval_sub]]

/-- Exact specialization-uniqueness contract for the positive Taylor steps.
If the denominator-cleared coefficient solves the specialized linear equation,
then it is the specialization of the recursively constructed numerator divided
by `q^(2t-1)`.  The concrete extraction proof only has to establish `hsolve`
for its Taylor forcing term. -/
theorem finiteTaylorNumerator_specialization_unique_succ {n : Nat}
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (a0 : Fin n → Polynomial F)
    (rhs : (t : Nat) →
      (Fin (t + 1) → Fin n → Polynomial F) → Fin n → Polynomial F)
    (z : F) (s : Nat) (x : Fin n → F)
    (hq : M.det.eval z ≠ 0)
    (hsolve : specializeMatrix z M *ᵥ
        ((M.det.eval z) ^ (2 * s) • x) =
      specializeVector z
        (rhs s (fun i => finiteTaylorNumerators M a0 rhs i.1))) :
    x = ((finiteTaylorDenominator M.det (s + 1)).eval z)⁻¹ •
      specializeVector z (finiteTaylorNumerators M a0 rhs (s + 1)) := by
  let b := rhs s (fun i => finiteTaylorNumerators M a0 rhs i.1)
  have hcramer := specialized_solution_cramer z M b
    ((M.det.eval z) ^ (2 * s) • x) hsolve
  have hnum :
      specializeVector z (finiteTaylorNumerators M a0 rhs (s + 1)) =
        M.det.eval z • ((M.det.eval z) ^ (2 * s) • x) := by
    simpa [finiteTaylorNumerators_succ, cramerStep, b] using hcramer
  rw [hnum]
  have hden :
      (finiteTaylorDenominator M.det (s + 1)).eval z =
        (M.det.eval z) ^ (2 * s + 1) := by
    simp [finiteTaylorDenominator, oddDenomExponent]
  rw [hden]
  funext i
  change x i = ((M.det.eval z) ^ (2 * s + 1))⁻¹ *
    (M.det.eval z * ((M.det.eval z) ^ (2 * s) * x i))
  have hp : M.det.eval z * ((M.det.eval z) ^ (2 * s) * x i) =
      (M.det.eval z) ^ (2 * s + 1) * x i := by
    rw [pow_succ']
    ring
  rw [hp]
  simp [hq]

theorem concreteTaylorNumerator_specialization_unique_succ
    (x₀ z : F) (R : TriPolynomial F) (h : Nat)
    (Hbar J : Polynomial (Polynomial F)) (a0 : Fin h → Polynomial F)
    (s : Nat) (x : Fin h → F)
    (hq : (multiplicationMatrix h Hbar J).det.eval z ≠ 0)
    (hsolve : specializeMatrix z (multiplicationMatrix h Hbar J) *ᵥ
        (((multiplicationMatrix h Hbar J).det.eval z) ^ (2 * s) • x) =
      specializeVector z
        (clearedTaylorForcing (multiplicationMatrix h Hbar J).det
          x₀ R h Hbar s
          (fun i => concreteTaylorNumerators x₀ R h Hbar J a0 i.1))) :
    x = ((finiteTaylorDenominator (multiplicationMatrix h Hbar J).det
        (s + 1)).eval z)⁻¹ •
      specializeVector z
        (concreteTaylorNumerators x₀ R h Hbar J a0 (s + 1)) := by
  simpa only [concreteTaylorNumerators] using
    finiteTaylorNumerator_specialization_unique_succ
      (multiplicationMatrix h Hbar J) a0
      (clearedTaylorForcing (multiplicationMatrix h Hbar J).det
        x₀ R h Hbar) z s x hq hsolve

/-- Outside a root of the determinant, the specialized multiplication matrix
has a unique solution for every right-hand side. -/
theorem specialized_mulVec_injective_of_det_ne_zero {n : Nat} (z : F)
    (M : Matrix (Fin n) (Fin n) (Polynomial F))
    (hq : M.det.eval z ≠ 0) : Function.Injective (specializeMatrix z M).mulVec := by
  intro x y hxy
  have hdet : (specializeMatrix z M).det ≠ 0 := by
    rw [det_specializeMatrix]
    exact hq
  have hz : specializeMatrix z M *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hv : x - y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  exact sub_eq_zero.mp hv

end

end ProximityPrize.SubmissionLower.FiniteTaylorExtraction
