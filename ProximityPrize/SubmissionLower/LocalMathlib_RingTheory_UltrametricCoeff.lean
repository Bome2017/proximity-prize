/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_UDecomposition
import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_RatFunc_Valuation

/-!
# The ultrametric step: coefficients of an integral element are integral

The heart of the infinity chart.  If `f = ∑_{j < q} (d j) ^ q * u ^ j` lies
in the valuation ring at infinity, then so does every `d j`.

The reason is that the terms have PAIRWISE DISTINCT valuations.  Writing
`u = X⁻¹`, the `j`-th term has `intDegree = q * intDegree (d j) - j`, and
those are distinct modulo `q` for `j < q`.  A sum with a unique maximal
term valuation has exactly that valuation (`Valuation.map_sum_eq_of_lt`),
so `v f ≤ 1` forces the maximum — hence every term — down to `≤ 1`, and
then `q * intDegree (d j) ≤ j < q` gives `intDegree (d j) ≤ 0`.

* `term_intDegree` — the degree of a term;
* `coeff_mem_of_sum_mem` — the statement above.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibUltrametricCoeff

open scoped Classical

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K]

theorem intDegree_pow (d : RatFunc K) (hd : d ≠ 0) (n : ℕ) :
    (d ^ n).intDegree = n * d.intDegree := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hd) hd, ih]
      push_cast
      ring

/-- The infinity valuation of a nonzero element is `exp` of its degree. -/
theorem val_eq_exp (x : RatFunc K) (hx : x ≠ 0) :
    RatFunc.inftyValuation K x = WithZero.exp x.intDegree := by
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx]

/-- The degree of the `j`-th term. -/
theorem term_intDegree (q j : ℕ) (d : RatFunc K) (hd : d ≠ 0) :
    (d ^ q * ((RatFunc.X : RatFunc K)⁻¹) ^ j).intDegree = q * d.intDegree - j := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXi : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX
  rw [RatFunc.intDegree_mul (pow_ne_zero _ hd) (pow_ne_zero _ hXi),
    intDegree_pow K d hd q, intDegree_pow K _ hXi j,
    RatFunc.intDegree_inv, RatFunc.intDegree_X]
  ring

/-- **The coefficients of an integral element are integral.** -/
theorem coeff_mem_of_sum_mem (q : ℕ) (hq : 0 < q) (d : ℕ → RatFunc K)
    (hf : RatFunc.inftyValuation K
        (∑ j ∈ Finset.range q, (d j) ^ q * ((RatFunc.X : RatFunc K)⁻¹) ^ j) ≤ 1)
    (j : ℕ) (hj : j < q) :
    RatFunc.inftyValuation K (d j) ≤ 1 := by
  classical
  have hXi : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  set v := RatFunc.inftyValuation K with hv
  set g : ℕ → RatFunc K := fun i => (d i) ^ q * ((RatFunc.X : RatFunc K)⁻¹) ^ i with hg
  set deg : ℕ → ℤ := fun i => q * (d i).intDegree - i with hdeg
  -- valuation of a nonzero term
  have hgne : ∀ i, d i ≠ 0 → g i ≠ 0 := fun i h =>
    mul_ne_zero (pow_ne_zero _ h) (pow_ne_zero _ hXi)
  have hval : ∀ i, d i ≠ 0 → v (g i) = WithZero.exp (deg i) := by
    intro i hi
    have h1 : v (g i) = WithZero.exp ((g i).intDegree) := val_eq_exp K _ (hgne i hi)
    rw [h1, hg]
    congr 1
    exact term_intDegree K q i (d i) hi
  by_contra hcon
  have hdj0 : d j ≠ 0 := by
    intro h
    apply hcon
    rw [h, map_zero]
    exact zero_le_one
  have hpos : 0 < (d j).intDegree := by
    by_contra hle
    push Not at hle
    apply hcon
    rw [hv, val_eq_exp K _ hdj0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact hle
  set S : Finset ℕ := (Finset.range q).filter (fun i => d i ≠ 0) with hS
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hdj0⟩
  obtain ⟨jstar, hjstarS, hmax⟩ := S.exists_max_image deg ⟨j, hjS⟩
  have hjstar : d jstar ≠ 0 := (Finset.mem_filter.mp hjstarS).2
  have hjstarlt : jstar < q := Finset.mem_range.mp (Finset.mem_filter.mp hjstarS).1
  have hgjstar : v (g jstar) = WithZero.exp (deg jstar) := hval jstar hjstar
  -- the degrees are pairwise distinct
  have hdistinct : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → deg a ≠ deg b := by
    intro a ha b hb hab hEq
    have hal : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbl : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hdvd : (q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := by
      refine ⟨(d a).intDegree - (d b).intDegree, ?_⟩
      simp only [hdeg] at hEq
      linarith
    have hlt : |((a : ℤ) - (b : ℤ))| < (q : ℤ) := by
      rw [abs_lt]
      omega
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact hab (by omega)
  -- the maximum is strict
  have hstrict : ∀ i ∈ Finset.range q \ {jstar}, v (g i) < v (g jstar) := by
    intro i hi
    obtain ⟨hiq, hine⟩ := Finset.mem_sdiff.mp hi
    have hine' : i ≠ jstar := by simpa using hine
    by_cases hdi : d i = 0
    · have hzero : g i = 0 := by
        simp only [hg, hdi]
        rw [zero_pow hq.ne', zero_mul]
      rw [hzero, map_zero, hgjstar]
      exact zero_lt_iff.mpr WithZero.exp_ne_zero
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨hiq, hdi⟩
      rw [hval i hdi, hgjstar, WithZero.exp_lt_exp]
      exact lt_of_le_of_ne (hmax i hiS) (hdistinct i hiS jstar hjstarS hine')
  have hsum : v (∑ i ∈ Finset.range q, g i) = v (g jstar) :=
    Valuation.map_sum_eq_of_lt v (Finset.mem_range.mpr hjstarlt) hstrict
  rw [hsum, hgjstar, ← WithZero.exp_zero, WithZero.exp_le_exp] at hf
  -- contradiction with the offending index
  have hdegj : 0 < deg j := by
    simp only [hdeg]
    have h1 : (1 : ℤ) ≤ (d j).intDegree := hpos
    have h2 : (j : ℤ) < (q : ℤ) := by exact_mod_cast hj
    nlinarith
  have := le_trans (hmax j hjS) hf
  omega

end ProximityPrize.SubmissionLower.LocalMathlibUltrametricCoeff

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibUltrametricCoeff.coeff_mem_of_sum_mem
