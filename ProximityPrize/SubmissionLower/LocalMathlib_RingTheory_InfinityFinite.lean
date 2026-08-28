/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_InfinityPowFinite
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_PolynomialFinite

/-!
# The infinity chart: finiteness with no separability hypothesis

The capstone `integralClosure_finite_of_frobeniusBase` instantiated at the
base `A = InfinityBase K`.

Unlike the polynomial chart, the `σ` and the Noetherian hypothesis come for
free here: the `q`-power map is injective on a reduced ring, so corestricting
it to its image is already an isomorphism, and the image is therefore
isomorphic to the DVR itself.  The only real content was
`finite_over_frobRange`.

* `frobEquivIR` — the `q`-power isomorphism;
* `infinity_integralClosure_finite` — the statement
  `FixedCurveNormSum.infiniteNormalization_finite` needs with
  `Algebra.IsSeparable (RatFunc K) L` deleted.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibInfinityFinite

open LocalMathlibInfinityPowFinite LocalMathlibUniformInseparableExponent
open LocalMathlibFiniteNoSeparable

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

attribute [local instance] charP_IR expChar_IR

/-- The `q`-power map corestricted to its image. -/
noncomputable def frobHomIR : IR K →+* frobRange K p e :=
  (iterateFrobenius (IR K) p e).codRestrict (frobRange K p e) (fun a => ⟨a, rfl⟩)

theorem frobHomIR_injective : Function.Injective (frobHomIR K p e) := by
  intro a b hab
  have h : a ^ p ^ e = b ^ p ^ e :=
    congrArg (fun z : frobRange K p e => (z : IR K)) hab
  exact iterateFrobenius_inj (IR K) p e h

theorem frobHomIR_surjective : Function.Surjective (frobHomIR K p e) := by
  rintro ⟨g, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

/-- **The `q`-power map is a ring isomorphism onto the subring of `q`-th
powers.** -/
noncomputable def frobEquivIR : IR K ≃+* frobRange K p e :=
  RingEquiv.ofBijective (frobHomIR K p e)
    ⟨frobHomIR_injective K p e, frobHomIR_surjective K p e⟩

theorem frobRange_isNoetherianRing : IsNoetherianRing (frobRange K p e) :=
  isNoetherianRing_of_ringEquiv (IR K) (frobEquivIR K p e)

/-- **Infinity-chart finiteness with no separability hypothesis.** -/
theorem infinity_integralClosure_finite (P : ℕ) [hP : Fact P.Prime] [CharP K P]
    [PerfectRing K P] (L : Type*) [Field L]
    [Algebra (IR K) L] [Algebra (RatFunc K) L]
    [IsScalarTower (IR K) (RatFunc K) L] [FiniteDimensional (RatFunc K) L] :
    Module.Finite (IR K) (integralClosure (IR K) L) := by
  classical
  haveI : IsFractionRing (IR K) (RatFunc K) :=
    InfinityValuationRing.infinityRing_isFractionRing K
  haveI hRF : CharP (RatFunc K) P :=
    charP_of_injective_algebraMap
      (IsFractionRing.injective (Polynomial K) (RatFunc K)) P
  haveI : CharP L P :=
    charP_of_injective_algebraMap (algebraMap (RatFunc K) L).injective P
  haveI : ExpChar L P := ExpChar.prime hP.out
  set M := separableClosure (RatFunc K) L with hM
  haveI : CharP M P :=
    charP_of_injective_algebraMap (algebraMap (RatFunc K) M).injective P
  haveI : ExpChar M P := ExpChar.prime hP.out
  haveI : IsPurelyInseparable M L := separableClosure.isPurelyInseparable (RatFunc K) L
  haveI : FiniteDimensional M L := FiniteDimensional.right (RatFunc K) M L
  obtain ⟨E, hE⟩ := exists_uniform_exponent M L P
  refine integralClosure_finite_of_frobeniusBase (F := RatFunc K) P E
    (frobRange K P E) (frobEquivIR K P E) (fun a => rfl)
    (frobRange_isNoetherianRing K P E)
    (finite_over_frobRange K P E)
    (fun x => ?_)
  obtain ⟨y, hy⟩ := hE x
  rw [← hy]
  exact y.2

end ProximityPrize.SubmissionLower.LocalMathlibInfinityFinite

#print axioms ProximityPrize.SubmissionLower.LocalMathlibInfinityFinite.frobEquivIR
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInfinityFinite.frobRange_isNoetherianRing

#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibInfinityFinite.infinity_integralClosure_finite
