/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_SeparablePartFinite

/-!
# The `q`-power map is a ring isomorphism `K[X] ≃+* K[X ^ q]`

Seventh unit: the `σ` that `finite_of_frobenius_descent` consumes.

`LocalMathlib_RingTheory_ExpandFrobenius` shows the `q`-power map lands in
`K[X ^ q]` and, over a perfect `K`, hits everything there.  It is injective
because `K[X]` is reduced.  Corestricting therefore gives a ring
isomorphism, which is exactly the `σ : A ≃+* A₀` the descent needs — and it
also transports Noetherianity to `A₀`, the other hypothesis of the descent.

* `frobEquiv` — `Polynomial K ≃+* expandRange K (p ^ e)`;
* `expandRange_isNoetherianRing` — hence `K[X ^ q]` is Noetherian.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.LocalMathlibExpandEquiv

open Polynomial LocalMathlibExpandFinite LocalMathlibExpandFrobenius

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] (p e : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The `q`-power map on `K[X]`, corestricted to `K[X ^ q]`. -/
noncomputable def frobHom : Polynomial K →+* expandRange K (p ^ e) :=
  (iterateFrobenius (Polynomial K) p e).codRestrict
    (expandRange K (p ^ e)) (fun f => pow_mem_expandRange K p e f)

theorem frobHom_apply (f : Polynomial K) :
    (frobHom K p e f : Polynomial K) = f ^ p ^ e := rfl

theorem frobHom_injective : Function.Injective (frobHom K p e) := by
  intro a b hab
  have h : a ^ p ^ e = b ^ p ^ e := congrArg (fun z : expandRange K (p ^ e) =>
    (z : Polynomial K)) hab
  exact iterateFrobenius_inj (Polynomial K) p e h

theorem frobHom_surjective : Function.Surjective (frobHom K p e) := by
  rintro ⟨g, hg⟩
  obtain ⟨f, hf⟩ := exists_pow_eq_of_mem_expandRange K p e g hg
  exact ⟨f, Subtype.ext hf⟩

/-- **The `q`-power map is a ring isomorphism onto `K[X ^ q]`.** -/
noncomputable def frobEquiv : Polynomial K ≃+* expandRange K (p ^ e) :=
  RingEquiv.ofBijective (frobHom K p e)
    ⟨frobHom_injective K p e, frobHom_surjective K p e⟩

/-- `K[X ^ q]` is Noetherian, being isomorphic to `K[X]`. -/
theorem expandRange_isNoetherianRing :
    IsNoetherianRing (expandRange K (p ^ e)) :=
  isNoetherianRing_of_ringEquiv (Polynomial K) (frobEquiv K p e)

end ProximityPrize.SubmissionLower.LocalMathlibExpandEquiv

#print axioms ProximityPrize.SubmissionLower.LocalMathlibExpandEquiv.frobEquiv
#print axioms
  ProximityPrize.SubmissionLower.LocalMathlibExpandEquiv.expandRange_isNoetherianRing
