/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower

/-!
# Separability from a simple root, with no degree bound

The contact ledger currently buys separability from
`integral_and_separable_of_small_annihilator`: a nonzero annihilator of
degree `< p` forces separability, because an inseparable irreducible
polynomial is a polynomial in `X ^ p` and so has degree `≥ p`.  Applied to
`Res (G, T)` that becomes the mixed-bidegree gate

    `T.degreeOf j * G.degreeOf k + G.degreeOf j * T.degreeOf k < p`,

which at the profile reduces to `yCap * seedTotalCap < 4064` and is the
binding constraint on the whole certificate.

There is a second, incomparable sufficient condition that carries **no
degree bound at all**: an element annihilated by `f` at which `f'` does not
vanish is separable.  The reason is short — if the minimal polynomial `g`
were inseparable then `g' = 0`, so writing `f = g * h` gives
`f' = g * h'`, and `f'` vanishes at `y` because `g` does.

* `isSeparable_of_aeval_derivative_ne_zero` — the statement above.

It is INCOMPARABLE to the existing gate, not a strengthening: neither
`f.natDegree < p` nor `aeval y f.derivative ≠ 0` implies the other.  So the
ledger can take the disjunction, discharging `PlaneRootSeparability
.integral_and_separable_of_small_annihilator` on one branch and this on the
other.

This is the keystone for replacing a global degree bound by a pointwise
transversality condition.  Nothing here is a `ProtocolClaim`, an alignment
bound, or a submission.
-/

namespace ProximityPrize.SubmissionLower.PlaneSimpleRootSeparability

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element annihilated by `f` is integral. -/
theorem isIntegral_of_aeval_eq_zero {f : K[X]} (y : L) (hf : f ≠ 0)
    (hroot : aeval y f = 0) : IsIntegral K y :=
  (IsAlgebraic.isIntegral ⟨f, hf, hroot⟩)

/-- **Separability from a simple root.**  If `f` annihilates `y` but its
derivative does not, then `y` is separable over `K` — no bound on
`f.natDegree` relative to the characteristic is required. -/
theorem isSeparable_of_aeval_derivative_ne_zero {f : K[X]} (y : L) (hf : f ≠ 0)
    (hroot : aeval y f = 0) (hderiv : aeval y f.derivative ≠ 0) :
    IsSeparable K y := by
  classical
  have hint : IsIntegral K y := isIntegral_of_aeval_eq_zero y hf hroot
  set g : K[X] := minpoly K y with hg
  have hgirr : Irreducible g := minpoly.irreducible hint
  -- the minimal polynomial divides every annihilator
  obtain ⟨h, hfh⟩ : g ∣ f := minpoly.dvd K y hroot
  -- if `g` were inseparable its derivative would vanish identically
  by_contra hsep
  have hgd : g.derivative = 0 := by
    by_contra hne
    exact hsep ((Polynomial.separable_iff_derivative_ne_zero hgirr).mpr hne)
  -- then `f' = g * h'`, which vanishes at `y`
  have hfd : f.derivative = g * h.derivative := by
    rw [hfh, derivative_mul, hgd, zero_mul, zero_add]
  apply hderiv
  rw [hfd, map_mul, minpoly.aeval K y, zero_mul]

end ProximityPrize.SubmissionLower.PlaneSimpleRootSeparability

#print axioms
  ProximityPrize.SubmissionLower.PlaneSimpleRootSeparability.isSeparable_of_aeval_derivative_ne_zero
