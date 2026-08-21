import ProximityPrize.SubmissionLower.FiniteTaylorExtraction
import ProximityPrize.SubmissionLower.FiniteTaylorAlignmentAssembly
import ProximityPrize.SubmissionLower.FiniteTaylorMonicize
import ProximityPrize.SubmissionLower.FiniteTaylorFactorQBridge
import ProximityPrize.SubmissionLower.FiniteTaylorCap72Height
import ProximityPrize.SubmissionLower.Cap72BadRoots5314

/-!
# Concrete finite-Taylor extraction for the 53.14 target

This file contains the branch-independent glue needed by the final extraction.
In particular, it records the exact three exceptional-polynomial budget and
the polynomial (rather than pointwise) endpoint of the integral Taylor
construction.  The remaining branch-specific obligations are deliberately
kept visible at the end of the file.
-/

namespace ProximityPrize.SubmissionLower.Target5314Extraction

open scoped BigOperators
open Polynomial ProximityPrize.Benchmark
open FactorThreshold5314
open FiniteTaylorCore FiniteTaylorExtraction
open FiniteTaylorAlignmentAssembly

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

variable {F : Type*} [Field F]

/-- Retain the points of `S` at which `f` does not vanish. -/
def retainNonroots [DecidableEq F] (S : Finset F) (f : Polynomial F) : Finset F :=
  S.filter fun z => f.eval z ≠ 0

/-- Removing the roots of one nonzero polynomial loses at most its degree. -/
theorem card_le_card_retainNonroots_add_natDegree [Fintype F] [DecidableEq F]
    (S : Finset F) (f : Polynomial F) (hf : f ≠ 0) :
    S.card ≤ (retainNonroots S f).card + f.natDegree := by
  classical
  let rootsIn := S.filter fun z => f.eval z = 0
  have hpartition : (retainNonroots S f).card + rootsIn.card = S.card := by
    simpa only [retainNonroots, rootsIn, not_ne_iff] using
      (S.card_filter_add_card_filter_not (fun z => f.eval z ≠ 0))
  have hroots : rootsIn.val ⊆ f.roots := by
    intro z hz
    exact (Polynomial.mem_roots hf).mpr (Finset.mem_filter.mp hz).2
  have hrootCard : rootsIn.card ≤ f.natDegree :=
    Polynomial.card_le_degree_of_subset_roots hroots
  omega

/-- The concrete three-stage good-seed filter: leading coefficient, simple
root resultant, then Cramer determinant. -/
def goodSeeds [DecidableEq F] (branch : Finset F)
    (W simple q : Polynomial F) : Finset F :=
  retainNonroots (retainNonroots (retainNonroots branch W) simple) q

theorem goodSeeds_subset [DecidableEq F] (branch : Finset F)
    (W simple q : Polynomial F) : goodSeeds branch W simple q ⊆ branch := by
  intro z hz
  exact (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1

theorem goodSeeds_eval_ne_zero [DecidableEq F]
    (branch : Finset F) (W simple q : Polynomial F) {z : F}
    (hz : z ∈ goodSeeds branch W simple q) :
    W.eval z ≠ 0 ∧ simple.eval z ≠ 0 ∧ q.eval z ≠ 0 := by
  exact ⟨(Finset.mem_filter.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2,
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2,
    (Finset.mem_filter.mp hz).2⟩

/-- The corrected second-branch margin pays for all three exceptional sets.
The deliberately loose determinant allowance is the source of the `2^45`
margin in `branchThreshold`. -/
theorem two_pow_fifty_lt_card_goodSeeds
    [Fintype F] [DecidableEq F]
    (branch : Finset F) (W simple q : Polynomial F)
    (hbranch : branchThreshold < branch.card)
    (hW : W ≠ 0) (hsimple : simple ≠ 0) (hq : q ≠ 0)
    (hWdeg : W.natDegree ≤ 72)
    (hsimpleDeg : simple.natDegree ≤ 1512)
    (hqdeg : q.natDegree ≤ 400000) :
    2 ^ 50 < (goodSeeds branch W simple q).card := by
  have h1 := card_le_card_retainNonroots_add_natDegree branch W hW
  have h2 := card_le_card_retainNonroots_add_natDegree
    (retainNonroots branch W) simple hsimple
  have h3 := card_le_card_retainNonroots_add_natDegree
    (retainNonroots (retainNonroots branch W) simple) q hq
  dsimp only [goodSeeds]
  unfold branchThreshold at hbranch
  omega

/-- Recenter the outer Taylor variable back from `S = X - x₀` to `X`. -/
def unshiftTaylor (x₀ : F)
    (S : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (Polynomial F)) :=
  S.comp (Polynomial.X -
    Polynomial.C (Polynomial.C (Polynomial.C x₀)))

theorem natDegree_unshiftTaylor_le (x₀ : F)
    (S : Polynomial (Polynomial (Polynomial F))) :
    (unshiftTaylor x₀ S).natDegree ≤ S.natDegree := by
  unfold unshiftTaylor
  exact Polynomial.natDegree_comp_le.trans (by simp)

theorem map_unshiftTaylor (x₀ z y : F)
    (S : Polynomial (Polynomial (Polynomial F))) :
    (unshiftTaylor x₀ S).map (FiniteTaylorExtraction.evalZT z y) =
      (S.map (FiniteTaylorExtraction.evalZT z y)).comp
        (Polynomial.X - Polynomial.C x₀) := by
  unfold unshiftTaylor
  rw [Polynomial.map_comp]
  simp [FiniteTaylorExtraction.evalZT]

theorem translatePolynomial_comp_X_sub_C (x₀ : F) (p : Polynomial F) :
    (translatePolynomial x₀ p).comp
      (Polynomial.X - Polynomial.C x₀) = p := by
  change (p.comp (Polynomial.X + Polynomial.C x₀)).comp
    (Polynomial.X - Polynomial.C x₀) = p
  rw [Polynomial.comp_assoc]
  have hi : (Polynomial.X + Polynomial.C x₀).comp
      (Polynomial.X - Polynomial.C x₀) = (Polynomial.X : Polynomial F) := by
    simp [Polynomial.add_comp]
  rw [hi, Polynomial.comp_X]

/-- The concrete monicization used by extraction inherits irreducibility over
the coefficient fraction field from the normalized second-branch factor. -/
theorem integralMonicize_fraction_irreducible
    (H : Polynomial (Polynomial F)) (hHirr : Irreducible H)
    (hHpos : 0 < H.natDegree) :
    Irreducible
      ((integralMonicize H).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) := by
  have hbase : Irreducible (integralMonicize H) := by
    simpa [integralMonicize,
      FiniteTaylorMonicize.integralMonicizeAux] using
      (FiniteTaylorMonicize.irreducible_integralMonicizeAux H hHirr hHpos)
  have hprimitive : (integralMonicize H).IsPrimitive :=
    hbase.isPrimitive (by
      rw [integralMonicize_natDegree]
      exact Nat.ne_of_gt hHpos)
  exact (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing (Polynomial F)) hprimitive).mp hbase

theorem integralMonicize_polyHeight_le_792
    (H : Polynomial (Polynomial F)) (hHdeg : H.natDegree ≤ 11)
    (hHheight : ∀ i, (H.coeff i).natDegree ≤ 72) :
    polyHeight (integralMonicize H) ≤ 792 := by
  simpa [integralMonicize,
    FiniteTaylorMonicize.integralMonicizeAux] using
    (FiniteTaylorMonicize.integralMonicizeAux_polyHeight_le_792
      H hHdeg hHheight)

/-- If the Taylor polynomial is already represented in the canonical quotient
basis, monic reduction is literally the identity.  This avoids any artificial
height growth in the final beta polynomial. -/
theorem canonicalRemainder_eq_self_of_degree_lt
    (H P : Polynomial (Polynomial F)) (hH : H.Monic)
    (hdegree : P.degree < H.degree) :
    canonicalRemainder H P = P := by
  exact (Polynomial.modByMonic_eq_self_iff hH).mpr hdegree

theorem polyHeight_sub_le (P Q : Polynomial (Polynomial F)) :
    polyHeight (P - Q) ≤ max (polyHeight P) (polyHeight Q) := by
  simpa only [sub_eq_add_neg, polyHeight_neg] using
    (polyHeight_add_le P (-Q))

/-- Concrete beta-height endpoint once canonical reduction is known to be
vacuous.  The `+1` is exactly the seed-variable degree of the affine row
value `row₀ + Z row₁`. -/
theorem canonical_beta_height_le
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (Hbar : Polynomial (Polynomial IRSProfile.Field)) (hHbar : Hbar.Monic)
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field)
    (hGeval : ∀ s, polyHeight
      (G.eval (Polynomial.C (Polynomial.C s))) ≤ 10104857200000)
    (hscale : scale.natDegree + 1 ≤ 10104857200000)
    (hpredegree : ∀ i,
      (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
        Polynomial.C
          (scale * (Polynomial.C (rows 0 i) +
            Polynomial.X * Polynomial.C (rows 1 i)))).degree < Hbar.degree) :
    ∀ i j,
      ((canonicalRemainder Hbar
        (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
          Polynomial.C
            (scale * (Polynomial.C (rows 0 i) +
              Polynomial.X * Polynomial.C (rows 1 i))))).coeff j).natDegree ≤
        10104857200000 := by
  intro i j
  let affine := Polynomial.C (rows 0 i) +
    Polynomial.X * Polynomial.C (rows 1 i)
  let D := G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
    Polynomial.C (scale * affine)
  have hrem : canonicalRemainder Hbar D = D :=
    canonicalRemainder_eq_self_of_degree_lt Hbar D hHbar (hpredegree i)
  change ((canonicalRemainder Hbar D).coeff j).natDegree ≤ 10104857200000
  rw [hrem]
  apply (natDegree_coeff_le_height D j).trans
  apply (polyHeight_sub_le _ _).trans
  apply max_le
  · exact hGeval (IRSProfile.domain i)
  · rw [polyHeight_C]
    exact Polynomial.natDegree_mul_le.trans (by
      apply Nat.add_le_add_left
      change affine.natDegree ≤ 1
      unfold affine
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)) |>.trans hscale

theorem cap72_scale_natDegree_add_one_le
    (q W : Polynomial F) (hqdeg : q.natDegree ≤ 400000)
    (hWdeg : W.natDegree ≤ 72) :
    (q ^ oddDenomExponent 131071 * W).natDegree + 1 ≤
      10104857200000 := by
  have hpow : (q ^ oddDenomExponent 131071).natDegree ≤
      262141 * 400000 := by
    refine Polynomial.natDegree_pow_le.trans ?_
    norm_num [oddDenomExponent]
    exact Nat.mul_le_mul_left 262141 hqdeg
  exact Nat.add_le_add_right
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hpow hWdeg)) 1 |>.trans
      (by norm_num)

/-- The coefficient-height premise consumed by the final filtered alignment
assembly, packaged so the concrete Taylor endpoint can export it without a
cyclic dependency on the final wrapper. -/
structure BetaHeightContract
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (Hbar : Polynomial (Polynomial IRSProfile.Field))
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field) : Prop where
  bound : ∀ i j,
    ((canonicalRemainder Hbar
      (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
        Polynomial.C
          (scale * (Polynomial.C (rows 0 i) +
            Polynomial.X * Polynomial.C (rows 1 i))))).coeff j).natDegree ≤
      10104857200000

/-- Named package for the concrete Taylor endpoint.  A structure avoids the
kernel-normalization blowup caused by repeatedly projecting a large nested
conjunction whose fields contain the full Taylor construction. -/
structure ConcreteTaylorEndpointContract
    (rows : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    {branch : Finset IRSProfile.Field}
    (x₀ : IRSProfile.Field)
    (pAt : IRSProfile.Field → Polynomial IRSProfile.Field)
    (W : Polynomial IRSProfile.Field)
    (Hbar : Polynomial (Polynomial IRSProfile.Field))
    (simple q : Polynomial IRSProfile.Field)
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field) : Prop where
  Gdegree : G.natDegree ≤ 131071
  Geval : ∀ s, polyHeight
    (G.eval (Polynomial.C (Polynomial.C s))) ≤ 10104857200000
  predegree : ∀ i,
    (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
      Polynomial.C
        (scale * (Polynomial.C (rows 0 i) +
          Polynomial.X * Polynomial.C (rows 1 i)))).degree < Hbar.degree
  betaHeight : BetaHeightContract rows Hbar G scale
  Gseed : ∀ gamma, ∀ hgamma : gamma ∈ goodSeeds branch W simple q,
    G.map (evalZT gamma
        (W.eval gamma * (pAt gamma).eval x₀)) =
      Polynomial.C (scale.eval gamma) * pAt gamma

theorem derivative_coeff_height_le
    (P : Polynomial (Polynomial F)) {D : Nat}
    (hcoeff : ∀ i, (P.coeff i).natDegree ≤ D) (i : Nat) :
    (P.derivative.coeff i).natDegree ≤ D := by
  rw [Polynomial.coeff_derivative]
  apply Polynomial.natDegree_mul_le.trans
  have hc : ((i : Polynomial F) + 1).natDegree ≤ 0 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  exact (Nat.add_le_add (hcoeff (i + 1)) hc).trans (by simp)

/-- Dependency-clean degree budget for the multiple-root exceptional
resultant.  Keeping the proof generic in the field avoids expensive reduction
of concrete extension-field numerals. -/
theorem simpleRootResultant_natDegree_le_1512
    (P : Polynomial (Polynomial F))
    (hPdeg : P.natDegree ≤ 11)
    (hPheight : ∀ i, (P.coeff i).natDegree ≤ 72) :
    (Polynomial.resultant P P.derivative P.natDegree
      (P.natDegree - 1)).natDegree ≤ 1512 := by
  apply (FiniteTaylorResultantRigidity.natDegree_resultant_le_asymmetric
    P P.derivative P.natDegree (P.natDegree - 1) 72 72 hPheight
      (derivative_coeff_height_le P hPheight)).trans
  omega

theorem simpleRootResultant_ne_zero
    (P : Polynomial (Polynomial IRSProfile.Field))
    (hPpos : 0 < P.natDegree) (hPdeg : P.natDegree ≤ 11)
    (hPsep : (SequentialFactorSelection.fractionMap P).Separable) :
    FiniteTaylorFactorQBridge.simpleRootResultant P ≠ 0 := by
  let K := FractionRing (Polynomial IRSProfile.Field)
  let φ : Polynomial IRSProfile.Field →+* K :=
    algebraMap (Polynomial IRSProfile.Field) K
  have hφinj : Function.Injective φ :=
    IsFractionRing.injective (Polynomial IRSProfile.Field) K
  have hPmapdeg : (SequentialFactorSelection.fractionMap P).natDegree =
      P.natDegree := Polynomial.natDegree_map_eq_of_injective hφinj P
  have hderivdeg :=
    FiniteTaylorFactorQBridge.fractionMap_derivative_natDegree_eq_sub_one
      P hPpos hPdeg
  have hres : Polynomial.resultant
      (SequentialFactorSelection.fractionMap P)
      (SequentialFactorSelection.fractionMap P).derivative
      P.natDegree (P.natDegree - 1) ≠ 0 := by
    simpa [hPmapdeg, hderivdeg] using Polynomial.resultant_ne_zero
      (SequentialFactorSelection.fractionMap P)
      (SequentialFactorSelection.fractionMap P).derivative hPsep
  intro hz
  apply hres
  change Polynomial.resultant (P.map φ) (P.map φ).derivative
    P.natDegree (P.natDegree - 1) = 0
  rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
  change φ (FiniteTaylorFactorQBridge.simpleRootResultant P) = 0
  simp [hz]

theorem quotientVariableVector_height_le_1000
    (h : Nat) (Hbar : Polynomial (Polynomial F))
    (hh : 0 < h) (hHdeg : Hbar.natDegree = h)
    (hHbar : Hbar.Monic) (hHheight : polyHeight Hbar ≤ 792) :
    vectorHeight (quotientVariableVector h Hbar) ≤ 1000 := by
  rw [vectorHeight_le_iff]
  intro i
  by_cases htwo : 2 ≤ h
  · have hXdeg : (Polynomial.X : Polynomial (Polynomial F)).degree <
        Hbar.degree := by
      rw [Hbar.degree_eq_natDegree hHbar.ne_zero, hHdeg]
      simp
      omega
    rw [quotientVariableVector,
      FiniteTaylorCore.canonicalRemainder_eq_self hHbar hXdeg]
    simp only [Polynomial.coeff_X]
    split <;> simp
  · have hone : h = 1 := by omega
    have hdegree : Hbar.degree = 1 := by
      rw [Hbar.degree_eq_natDegree hHbar.ne_zero, hHdeg, hone]
      simp
    let a : Polynomial F := -Hbar.coeff 0
    have hform : Hbar = Polynomial.X - Polynomial.C a := by
      apply Polynomial.ext
      intro n
      rcases n with _ | n
      · simp [a]
      · rcases n with _ | n
        · have hcoeff : Hbar.coeff 1 = 1 := by
            have hc := hHbar.coeff_natDegree
            rw [hHdeg, hone] at hc
            exact hc
          simpa [a, hcoeff]
        · have hn : Hbar.coeff (n + 2) = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [hHdeg, hone]
            omega
          simp [a, hn, Polynomial.coeff_X, Nat.add_assoc]
    have hrem : canonicalRemainder Hbar Polynomial.X = Polynomial.C a := by
      unfold canonicalRemainder
      rw [hform, Polynomial.modByMonic_X_sub_C_eq_C_eval]
      simp
    rw [quotientVariableVector, hrem]
    have hi0 : i.1 = 0 := by omega
    simp only [hi0, Polynomial.coeff_C_zero]
    change (-Hbar.coeff 0).natDegree ≤ 1000
    rw [Polynomial.natDegree_neg]
    exact (natDegree_coeff_le_height Hbar 0).trans hHheight |>.trans (by norm_num)

/-- Polynomial endpoint of the integralized common-denominator Taylor
construction.  This is the map-level strengthening of the point-evaluation
endpoint and is what final coefficientwise quotient interpolation consumes. -/
theorem map_integralized_commonTaylorTruncation
    (x₀ z : F) (R : TriPolynomial F) (H : Polynomial (Polynomial F))
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
    (commonDenominatorTaylorTruncation h k q seq).map
      (evalZT z (H.leadingCoeff.eval z * p.eval x₀)) =
        Polynomial.C (q.eval z ^ oddDenomExponent k) *
          translatePolynomial x₀
            (Polynomial.C (H.leadingCoeff.eval z) * p) := by
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
  rw [map_commonDenominatorTaylorTruncation h k q seq z
    (H.leadingCoeff.eval z * p.eval x₀) g (by simpa [q] using hq) hseq]
  rw [truncatePolynomial_eq_self k g hgdeg]

/-- After recentering the outer variable, the mapped universal polynomial is
exactly the selected polynomial multiplied by the common Taylor denominator
and by the leading-coefficient scale. -/
theorem map_unshifted_integralized_commonTaylorTruncation
    (x₀ z : F) (R : TriPolynomial F) (H : Polynomial (Polynomial F))
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
    (unshiftTaylor x₀
      (commonDenominatorTaylorTruncation h k q seq)).map
        (evalZT z (H.leadingCoeff.eval z * p.eval x₀)) =
      Polynomial.C
          (q.eval z ^ oddDenomExponent k * H.leadingCoeff.eval z) * p := by
  dsimp only
  let Rbar := integralScale (Polynomial.C H.leadingCoeff) R
  let Hbar := integralMonicize H
  let J := derivativeAtX x₀ Rbar
  let q := (multiplicationMatrix h Hbar J).det
  let seq := concreteTaylorNumerators x₀ Rbar h Hbar J
    (quotientVariableVector h Hbar)
  rw [map_unshiftTaylor]
  rw [map_integralized_commonTaylorTruncation x₀ z R H h k hh hHdeg p
    hpdeg hHroot hRroot hq hJ]
  rw [Polynomial.mul_comp, Polynomial.C_comp,
    translatePolynomial_comp_X_sub_C]
  rw [← mul_assoc, Polynomial.C_mul]

/-! ## Final filtered alignment glue -/

/-- Once the three concrete exceptional polynomials and the fixed-resultant
degree estimate are available, all remaining rich-fiber and interpolation
assembly is formal.  In particular, the specialized beta-root hypothesis is
derived here from the selected witness's agreement property; it is not left
as an additional algebraic assumption. -/
theorem selectedPolynomialAlignment_of_filtered_taylor_data
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad branch : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hbranchSub : branch ⊆ bad)
    (W simple q : Polynomial IRSProfile.Field)
    (hbranchCard : branchThreshold < branch.card)
    (hW : W ≠ 0) (hsimple : simple ≠ 0) (hq : q ≠ 0)
    (hWdeg : W.natDegree ≤ 72)
    (hsimpleDeg : simple.natDegree ≤ 1512)
    (hqdeg : q.natDegree ≤ 400000)
    (Hbar : Polynomial (Polynomial IRSProfile.Field))
    (hHbarMonic : Hbar.Monic)
    (hHbarPos : 0 < Hbar.natDegree)
    (hHbarDeg : Hbar.natDegree ≤ 11)
    (hHbarHeight : polyHeight Hbar ≤ 792)
    (hHbarIrr : Irreducible
      (Hbar.map (algebraMap (Polynomial IRSProfile.Field)
        (FractionRing (Polynomial IRSProfile.Field)))))
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hGdegree : G.natDegree ≤ 131071)
    (yAt : IRSProfile.Field → IRSProfile.Field)
    (hHroot : ∀ gamma ∈ goodSeeds branch W simple q,
      (FiniteTaylorResultantRigidity.specializeZ gamma Hbar).eval
        (yAt gamma) = 0)
    (hGseed : ∀ gamma, ∀ hgamma : gamma ∈ goodSeeds branch W simple q,
      G.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom gamma)
          (yAt gamma)) =
        Polynomial.C
            ((q ^ oddDenomExponent 131071 * W).eval gamma) *
          (selected ⟨gamma,
            hbranchSub (goodSeeds_subset branch W simple q hgamma)⟩).polynomial)
    (support : IRSProfile.Field → Finset IRSProfile.Index)
    (hsupportEq : ∀ gamma, ∀ hgamma : gamma ∈ goodSeeds branch W simple q,
      support gamma =
        (selected ⟨gamma,
          hbranchSub (goodSeeds_subset branch W simple q hgamma)⟩).support)
    (hbetaHeight : BetaHeightContract rows Hbar G
      (q ^ oddDenomExponent 131071 * W)) :
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      p₀.degree < IRSProfile.baseDimension ∧
      p₁.degree < IRSProfile.baseDimension ∧
      ∃ aligned : Finset IRSProfile.Field,
        ∃ alignedSub : aligned ⊆ bad,
          Fintype.card IRSProfile.Index + 1 ≤ aligned.card ∧
          ∀ gamma, ∀ hgamma : gamma ∈ aligned,
            (selected ⟨gamma, alignedSub hgamma⟩).polynomial =
              p₀ + Polynomial.C gamma * p₁ := by
  classical
  let good := goodSeeds branch W simple q
  set scale := q ^ oddDenomExponent 131071 * W with hscaledef
  set beta : IRSProfile.Index → Polynomial (Polynomial IRSProfile.Field) :=
    fun i => canonicalRemainder Hbar
      (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
        Polynomial.C
          (scale * (Polynomial.C (rows 0 i) +
            Polynomial.X * Polynomial.C (rows 1 i)))) with hbetadef
  have hgoodSub : good ⊆ bad := by
    intro gamma hgamma
    exact hbranchSub (goodSeeds_subset branch W simple q hgamma)
  have hgoodCard : 2 ^ 50 < good.card := by
    exact two_pow_fifty_lt_card_goodSeeds branch W simple q hbranchCard
      hW hsimple hq hWdeg hsimpleDeg hqdeg
  have hscale : ∀ gamma ∈ good, scale.eval gamma ≠ 0 := by
    intro gamma hgamma
    obtain ⟨hWg, _, hqg⟩ := goodSeeds_eval_ne_zero branch W simple q hgamma
    simp only [scale, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hqg) hWg
  have hbetaDegree : ∀ i, (beta i).natDegree < Hbar.natDegree := by
    intro i
    apply Polynomial.natDegree_modByMonic_lt _ hHbarMonic
    intro hOne
    have : Hbar.natDegree = 0 := by simp [hOne]
    omega
  have hresultantDegree : ∀ i,
      (FiniteTaylorResultantRigidity.quotientResultant Hbar
        (beta i)).natDegree < 2 ^ 47 := by
    intro i
    apply FiniteTaylorResultantRigidity.quotientResultant_natDegree_lt_2pow47
      Hbar (beta i) hHbarDeg
        ((Nat.le_of_lt (hbetaDegree i)).trans hHbarDeg)
    · intro j
      exact (natDegree_coeff_le_height Hbar j).trans hHbarHeight
    · intro j
      let e := congrArg
        (fun b : Polynomial (Polynomial IRSProfile.Field) =>
          (b.coeff j).natDegree ≤ 10104857200000)
        (congrFun hbetadef i)
      exact Eq.mp e.symm (hbetaHeight.bound i j)
  have hbetaRoot : ∀ i gamma,
      i ∈ AgreementIncidence5314.richCoordinates good support (2 ^ 47) →
      gamma ∈ good → i ∈ support gamma →
      (FiniteTaylorResultantRigidity.specializeZ gamma (beta i)).eval
        (yAt gamma) = 0 := by
    intro i gamma _hi hgamma hisupport
    change (FiniteTaylorExtraction.specializeZ gamma (beta i)).eval
      (yAt gamma) = 0
    dsimp only [beta]
    rw [FiniteTaylorExtraction.eval_specializeZ_canonicalRemainder_at_root
      gamma (yAt gamma) Hbar _ (hHroot gamma hgamma)]
    have hagree :=
      (selected ⟨gamma, hgoodSub hgamma⟩).agrees i (by
        rw [← hsupportEq gamma hgamma]
        exact hisupport)
    have hseed := hGseed gamma hgamma
    change G.map (FiniteTaylorExtraction.evalZT gamma (yAt gamma)) =
      Polynomial.C (scale.eval gamma) *
        (selected ⟨gamma, hgoodSub hgamma⟩).polynomial at hseed
    rw [← FiniteTaylorExtraction.evalZT_eq_specializeZ_eval]
    have hcomm : FiniteTaylorExtraction.evalZT gamma (yAt gamma)
        (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i)))) =
        (G.map (FiniteTaylorExtraction.evalZT gamma (yAt gamma))).eval
          (IRSProfile.domain i) := by
      unfold Polynomial.eval
      rw [Polynomial.hom_eval₂]
      simp [FiniteTaylorExtraction.evalZT]
      rw [Polynomial.eval₂_eq_eval_map]
    rw [map_sub, hcomm, hseed]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [hagree]
    simp [scale, FiniteTaylorExtraction.evalZT,
      CoreDefinitions.AffineLineGenerator, Fin.sum_univ_two]
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_C]
    simp [Polynomial.evalRingHom]
    ring
  have hbetaZero : ∀ i,
      i ∈ AgreementIncidence5314.richCoordinates good support (2 ^ 47) →
        beta i = 0 := by
    refine rich_beta_eq_zero_of_fixed_resultants good support id
      (Set.injOn_id (good : Set IRSProfile.Field))
      Hbar hHbarIrr hHbarPos yAt hHroot beta hbetaDegree ?_
      hbetaRoot
    intro i
    exact hresultantDegree i
  refine selectedPolynomialAlignment_of_rich_quotient_data selected hgoodSub
    hgoodCard Hbar G scale yAt ?_ hscale hGdegree ?_ support ?_ ?_
  · intro gamma hgamma
    exact hHroot gamma hgamma
  · intro gamma hgamma
    change gamma ∈ goodSeeds branch W simple q at hgamma
    change G.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom gamma)
        (yAt gamma)) =
      Polynomial.C ((q ^ oddDenomExponent 131071 * W).eval gamma) *
        (selected ⟨gamma, hgoodSub hgamma⟩).polynomial
    exact hGseed gamma hgamma
  · intro gamma hgamma
    exact hsupportEq gamma hgamma
  · intro i hi
    exact hbetaZero i hi

end

end ProximityPrize.SubmissionLower.Target5314Extraction
