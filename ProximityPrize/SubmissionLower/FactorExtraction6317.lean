/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionLower.LinearCell6317

/-!
# Extracting a surface and a rational place from a decoded root

This is the global-to-local bridge omitted by the abstract Appendix-A argument.  A decoded
linear factor first lands in one primitive irreducible surface factor.  After the surface's
generic middle-coordinate specialization, either the scalar kills its content (paid globally)
or a positive-degree irreducible factor supplies the rational place used by the Hensel proof.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace FactorExtraction6317

open SurfaceFactors6317 Genericity6317
open RF6317 RF6317.HenselNumerators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem specializeZ_eq_content_mul_primPart
    (Q : F[X][X][Y]) (z : F) :
    specializeZ Q z =
      Polynomial.C (Bivariate.evalX z Q.content) * specializeZ Q.primPart z := by
  rw [Polynomial.eq_C_content_mul_primPart]
  simp [specializeZ, Bivariate.evalX_eq_map]

/-- Away from the single global content set, a specialized linear root is carried by one
primitive irreducible surface factor. -/
theorem exists_surface_factor_of_linear_dvd
    {Q : F[X][X][Y]} {z : F} {P : F[X]}
    (hQ : Q ≠ 0)
    (hz : z ∉ globalContentRootSet Q)
    (hdiv : Polynomial.X - Polynomial.C P ∣ specializeZ Q z) :
    ∃ R ∈ surfaceFactors Q,
      Polynomial.X - Polynomial.C P ∣ specializeZ R z := by
  classical
  let L : F[X][Y] := Polynomial.X - Polynomial.C P
  let c : F[X] := Bivariate.evalX z Q.content
  have hc : c ≠ 0 := by
    simpa [c, globalContentRootSet] using hz
  have hprime : Prime L := (Polynomial.irreducible_X_sub_C P).prime
  have hfac : L ∣ Polynomial.C c * specializeZ Q.primPart z := by
    simpa [L, c, specializeZ_eq_content_mul_primPart] using hdiv
  have hprim : L ∣ specializeZ Q.primPart z := by
    rcases hprime.dvd_mul.mp hfac with hconstant | hprimitive
    · have hC : (Polynomial.C c : F[X][Y]) ≠ 0 := Polynomial.C_ne_zero.mpr hc
      have hle := Polynomial.natDegree_le_of_dvd hconstant hC
      have hL : L.natDegree = 1 := by simp [L]
      omega
    · exact hprimitive
  let s := UniqueFactorizationMonoid.normalizedFactors Q.primPart
  let φ : F[X][X][Y] →+* F[X][Y] :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  have hassoc : Associated s.prod Q.primPart := by
    exact UniqueFactorizationMonoid.prod_normalizedFactors (Polynomial.primPart_ne_zero Q)
  have hassocMap : Associated (φ s.prod) (φ Q.primPart) := hassoc.map φ
  have hprod : L ∣ φ s.prod := by
    apply hassocMap.dvd_iff_dvd_right.mpr
    simpa [φ, specializeZ] using hprim
  have hmapped : L ∣ (s.map φ).prod := by
    simpa [map_multiset_prod] using hprod
  obtain ⟨R, hRs, hRdiv⟩ := hprime.exists_mem_multiset_map_dvd hmapped
  refine ⟨R, ?_, ?_⟩
  · simpa [surfaceFactors, s] using hRs
  · simpa [φ, specializeZ] using hRdiv

/-- Evaluation in `Z` followed by the decoded polynomial and evaluation in `X` commutes with
first specializing the middle variable. -/
theorem evalZY_specializeX_eq_eval_specializeR
    (R : F[X][X][Y]) (x z : F) (P : F[X]) :
    evalZY (specializeX x R) z (P.eval x) =
      ((specializeR R z).eval P).eval x := by
  classical
  induction R using Polynomial.induction_on' with
  | add A B hA hB =>
      simp [evalZY, specializeX_eq_map, specializeR, hA, hB]
  | monomial n A =>
      induction A using Polynomial.induction_on' with
      | add A B hA hB =>
          simp [evalZY, specializeX_eq_map, specializeR, hA, hB, add_mul]
      | monomial m a =>
          simp [evalZY, specializeX_eq_map, specializeR,
            Polynomial.coe_evalRingHom_apply, mul_pow]

theorem evalZY_specializeX_eq_zero_of_linear_dvd
    {R : F[X][X][Y]} {x z : F} {P : F[X]}
    (hdiv : Polynomial.X - Polynomial.C P ∣ specializeR R z) :
    evalZY (specializeX x R) z (P.eval x) = 0 := by
  rw [evalZY_specializeX_eq_eval_specializeR]
  have hroot : (specializeR R z).eval P = 0 := Polynomial.dvd_iff_isRoot.mp hdiv
  simp [hroot]

/-! ## Turning an `H`-root into a root of its integral monicization -/

theorem evalEval_monicize_scaled_eq_zero
    {H : F[X][Y]} {z y : F} (hpos : 0 < H.natDegree)
    (hroot : H.evalEval z y = 0) :
    (monicize H).evalEval z (H.leadingCoeff.eval z * y) = 0 := by
  classical
  let d := H.natDegree
  let w := H.leadingCoeff.eval z
  have hd : 0 < d := hpos
  have hroot' : w * y ^ d +
      ∑ i ∈ Finset.range d, (H.coeff i).eval z * y ^ i = 0 := by
    change (H.eval (Polynomial.C y)).eval z = 0 at hroot
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ] at hroot
    simpa [d, w, Polynomial.coeff_natDegree, add_comm] using hroot
  have htop : (w * y) ^ d = w ^ (d - 1) * (w * y ^ d) := by
    rw [mul_pow]
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
    rw [← hd', pow_add]
    ring
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      ((H.coeff i * H.leadingCoeff ^ (d - 1 - i)).eval z) * (w * y) ^ i =
        w ^ (d - 1) * ((H.coeff i).eval z * y ^ i) := by
    have hi' : i < d := Finset.mem_range.mp hi
    have hexp : d - 1 - i + i = d - 1 := by omega
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, mul_pow, w]
    rw [← pow_add, hexp]
    ring
  rw [monicize, if_neg (Nat.ne_of_gt hpos)]
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_pow,
    Polynomial.evalEval_X, Polynomial.evalEval_finsetSum,
    Polynomial.evalEval_mul, Polynomial.evalEval_C]
  rw [htop, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [← mul_add, hroot', mul_zero]

noncomputable def scaledRationalRoot
    {H : F[X][Y]} (hpos : 0 < H.natDegree) (z y : F)
    (hroot : H.evalEval z y = 0) : rationalRoot (monicize H) z :=
  ⟨H.leadingCoeff.eval z * y,
    evalEval_monicize_scaled_eq_zero hpos hroot⟩

@[simp] theorem scaledRationalRoot_value
    {H : F[X][Y]} (hpos : 0 < H.natDegree) (z y : F)
    (hroot : H.evalEval z y = 0) :
    (scaledRationalRoot hpos z y hroot).1 = H.leadingCoeff.eval z * y := rfl

end FactorExtraction6317
end ProximityPrize.SubmissionLower
