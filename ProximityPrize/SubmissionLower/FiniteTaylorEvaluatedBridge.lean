import ProximityPrize.SubmissionLower.FiniteTaylorExtraction
import ProximityPrize.SubmissionLower.SequentialFactorSelection
import ProximityPrize.SubmissionLower.FactorThreshold5314
import ProximityPrize.SubmissionLower.AgreementIncidence5314

/-!
# Scalar evaluation bridge for finite Taylor extraction

The Cramer recursion lives in the coefficient-vector model of
`F[Z][T]/(H)`.  A selected decoding polynomial supplies only one specialized
root `y₀` of `H`, so it cannot imply equality of quotient-coordinate vectors.
This file records the sound bridge: evaluate the quotient identities at that
root and use the nonvanishing specialized derivative for scalar uniqueness.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorEvaluatedBridge

open scoped BigOperators
open Polynomial Matrix
open FiniteTaylorCore FiniteTaylorExtraction

noncomputable section

variable {F : Type*} [Field F]

/-- Evaluation of a quotient-coordinate vector at a specialized ordinate. -/
def evalSpecializedVector (h : Nat) (z y : F)
    (v : Fin h → Polynomial F) : F :=
  evalZT z y (vectorPolynomial h v)

@[simp] theorem evalSpecializedVector_apply (h : Nat) (z y : F)
    (v : Fin h → Polynomial F) :
    evalSpecializedVector h z y v =
      ∑ i : Fin h, (v i).eval z * y ^ i.1 := by
  classical
  simp [evalSpecializedVector, evalZT, vectorPolynomial,
    Polynomial.eval₂_monomial]

/-- At a specialized root of `H`, canonical reduction modulo `H` does not
change scalar evaluation. -/
theorem evalZT_canonicalRemainder_of_root (z y : F)
    (H P : Polynomial (Polynomial F))
    (hroot : evalZT z y H = 0) :
    evalZT z y (canonicalRemainder H P) = evalZT z y P := by
  obtain ⟨K, hK⟩ := canonicalRemainder_congruent (H := H) P
  have hmapped := congrArg (evalZT z y) hK
  simp only [map_sub, map_mul, hroot, zero_mul] at hmapped
  exact sub_eq_zero.mp hmapped

/-- Multiplication matrices are sound after specializing and evaluating at
one root.  This is the valid scalar consequence of the quotient-vector
identity; no converse is asserted. -/
theorem evalSpecializedVector_multiplicationMatrix (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic)
    (hHdeg : H.natDegree = h) (J : Polynomial (Polynomial F))
    (z y : F) (hroot : evalZT z y H = 0)
    (v : Fin h → Polynomial F) :
    evalSpecializedVector h z y
        (multiplicationMatrix h H J *ᵥ v) =
      evalZT z y J * evalSpecializedVector h z y v := by
  unfold evalSpecializedVector
  rw [← multiplicationMatrix_represents_mul_mod h hh H hH hHdeg J v]
  rw [evalZT_canonicalRemainder_of_root z y H]
  exact map_mul (evalZT z y) J (vectorPolynomial h v)

/-- Evaluated division-free Cramer identity.  If `q=det(M)`, the next
numerator satisfies `J * A_next = q * forcing` at every specialized root of
`H`. -/
theorem evaluated_cramerStep_cross_multiply (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic)
    (hHdeg : H.natDegree = h) (J : Polynomial (Polynomial F))
    (z y : F) (hroot : evalZT z y H = 0)
    (b : Fin h → Polynomial F) :
    evalZT z y J *
        evalSpecializedVector h z y
          (cramerStep (multiplicationMatrix h H J) b) =
      (multiplicationMatrix h H J).det.eval z *
        evalSpecializedVector h z y b := by
  let M := multiplicationMatrix h H J
  have hvec := mulVec_adjugate_mulVec M b
  have heval := congrArg (evalSpecializedVector h z y) hvec
  have hleft := evalSpecializedVector_multiplicationMatrix
    h hh H hH hHdeg J z y hroot (M.adjugate *ᵥ b)
  rw [hleft] at heval
  simpa [cramerStep, M, evalSpecializedVector, vectorPolynomial_smul,
    evalZT] using heval

/-- Denominator-normalized form of the evaluated Cramer step.  The exponent
change `2s -> 2s+1` is explicit, so no quotient-vector converse is hidden. -/
theorem evaluated_cramerStep_divided (h : Nat) (hh : 0 < h)
    (H : Polynomial (Polynomial F)) (hH : H.Monic)
    (hHdeg : H.natDegree = h) (J : Polynomial (Polynomial F))
    (z y : F) (hroot : evalZT z y H = 0)
    (b : Fin h → Polynomial F) (s : Nat)
    (hq : (multiplicationMatrix h H J).det.eval z ≠ 0) :
    evalZT z y J *
        (((multiplicationMatrix h H J).det.eval z) ^ (2 * s + 1))⁻¹ *
          evalSpecializedVector h z y
            (cramerStep (multiplicationMatrix h H J) b) =
      (((multiplicationMatrix h H J).det.eval z) ^ (2 * s))⁻¹ *
        evalSpecializedVector h z y b := by
  have hcross := evaluated_cramerStep_cross_multiply
    h hh H hH hHdeg J z y hroot b
  have hqpow : ((multiplicationMatrix h H J).det.eval z) ^ (2 * s) ≠ 0 :=
    pow_ne_zero _ hq
  field_simp
  simpa [pow_succ'] using hcross

/-- If a power-series root is split into a known history `Γ` and a tail `δ`
of order at least `n`, then its `n`-th coefficient obeys the usual scalar
implicit-function equation. -/
theorem powerSeries_root_coefficient_equation {A B : Type*}
    [CommRing A] [Field B] (n : Nat) (hn : 1 ≤ n)
    (φ : A →+* PowerSeries B) (Γ δ : PowerSeries B)
    (hδ : ∀ i < n, PowerSeries.coeff i δ = 0)
    (P : Polynomial A)
    (hroot : PowerSeries.coeff n (Polynomial.eval₂ φ (Γ + δ) P) = 0) :
    PowerSeries.constantCoeff (Polynomial.eval₂ φ Γ P.derivative) *
        PowerSeries.coeff n δ =
      -PowerSeries.coeff n (Polynomial.eval₂ φ Γ P) := by
  have hsplit := powerSeries_coeff_eval₂_split n hn φ Γ δ hδ P
  rw [hroot] at hsplit
  linear_combination -hsplit

/-- The scalar recurrence at a simple root has a unique coefficient.  This is
the cancellation step used to identify the evaluated universal numerator
with the Taylor coefficient of a selected polynomial root. -/
theorem scalar_recurrence_unique (J rhs a g : F) (hJ : J ≠ 0)
    (ha : J * a = rhs) (hg : J * g = rhs) : a = g := by
  apply mul_left_cancel₀ hJ
  exact ha.trans hg.symm

/-- Direct identification contract: once the selected Taylor coefficient and
the evaluated universal Cramer coefficient satisfy the same recurrence away
from the derivative exception, they coincide. -/
theorem evaluated_universal_eq_selected_taylorCoeff
    (J rhs selectedCoeff universalCoeff : F) (hJ : J ≠ 0)
    (hselected : J * selectedCoeff = rhs)
    (huniversal : J * universalCoeff = rhs) :
    universalCoeff = selectedCoeff :=
  (scalar_recurrence_unique J rhs selectedCoeff universalCoeff hJ
    hselected huniversal).symm

/-! ## History recurrence and resultant rigidity

These lemmas deliberately separate the two logically different uses of a
specialized simple root.  Scalar recurrence uniqueness identifies Taylor
coefficients at that root.  A resultant, rather than evaluation injectivity on
the quotient-coordinate vector, promotes agreement at many seeds back to a
universal quotient identity.
-/

/-- Uniqueness of a history-dependent scalar recurrence.  The forcing at time
`t` may depend on the whole prefix through `t`; pointwise equality of that
prefix is the only congruence hypothesis required. -/
theorem scalar_history_recurrence_unique
    (J : F) (hJ : J ≠ 0)
    (forcing : Nat → (Nat → F) → F) (a g : Nat → F)
    (hzero : a 0 = g 0)
    (ha : ∀ t, J * a (t + 1) = forcing t a)
    (hg : ∀ t, J * g (t + 1) = forcing t g)
    (hforcing : ∀ t f₁ f₂,
      (∀ i, i ≤ t → f₁ i = f₂ i) → forcing t f₁ = forcing t f₂) :
    ∀ t, a t = g t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
      cases t with
      | zero => exact hzero
      | succ s =>
          apply mul_left_cancel₀ hJ
          calc
            J * a (s + 1) = forcing s a := ha s
            _ = forcing s g := hforcing s a g (by
              intro i hi
              exact ih i (by omega))
            _ = J * g (s + 1) := (hg s).symm

/-- A nonzero univariate polynomial cannot vanish on more injectively chosen
field points than its degree.  This is the root-count step used for every
exceptional/resultant polynomial in the extraction argument. -/
theorem polynomial_eq_zero_of_many_evaluations
    {Seed : Type*} [DecidableEq Seed]
    (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (P : Polynomial F) (hcard : P.natDegree < seeds.card)
    (hvanish : ∀ seed ∈ seeds, P.eval (z seed) = 0) :
    P = 0 := by
  classical
  by_contra hP
  have himage : (seeds.image z).card = seeds.card :=
    Finset.card_image_iff.mpr hz
  have hroots : (seeds.image z).val ⊆ P.roots := by
    intro root hroot
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp
      (show root ∈ seeds.image z from hroot)
    exact (Polynomial.mem_roots hP).mpr (hvanish seed hseed)
  have hle : seeds.card ≤ P.natDegree := by
    rw [← himage]
    exact Polynomial.card_le_degree_of_subset_roots hroots
  omega

/-- Resultant promotion, kept separate from
the root-count lemma so the algebraic `resultant = 0 → beta = 0` proof can
be audited independently. -/
theorem quotient_representative_eq_zero_of_many_resultant_roots
    {Seed : Type*} [DecidableEq Seed]
    (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (resultantWitness : Polynomial F)
    (hcard : resultantWitness.natDegree < seeds.card)
    (hresultantRoot : ∀ seed ∈ seeds,
      resultantWitness.eval (z seed) = 0)
    {A : Type*} [Zero A] (beta : A)
    (resultantZero_forces : resultantWitness = 0 → beta = 0) :
    beta = 0 := by
  apply resultantZero_forces
  exact polynomial_eq_zero_of_many_evaluations seeds z hz resultantWitness
    hcard hresultantRoot

/-- Once quotient-resultant rigidity gives equality at `k+1` distinct
coordinates, bounded-degree polynomials agree globally. -/
theorem polynomial_eq_of_many_evaluations
    {Index : Type*} [Fintype Index]
    (x : Index → F) (hx : Function.Injective x)
    (p g : Polynomial F)
    (hdegree : max p.natDegree g.natDegree < Fintype.card Index)
    (heval : ∀ i, p.eval (x i) = g.eval (x i)) :
    p = g := by
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq p g hx heval hdegree

/-! ## Common-denominator coordinate evaluation -/

theorem truncatePolynomial_eq_self_of_natDegree_le (k : Nat)
    (g : Polynomial F) (hg : g.natDegree ≤ k) :
    truncatePolynomial k g = g := by
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ k
  · exact truncatePolynomial_coeff_of_le k i g hi
  · have hgzero : g.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hgzero]
    unfold truncatePolynomial
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [if_neg]
    intro hji
    subst i
    omega

/-- Substitute a scalar displacement into the universal Taylor truncation,
leaving the quotient variables `Z,T`. -/
def evaluateTaylorAt (s : F)
    (G : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial F) :=
  G.eval (Polynomial.C (Polynomial.C s))

theorem evalZT_evaluateTaylorAt (s z y : F)
    (G : Polynomial (Polynomial (Polynomial F))) :
    evalZT z y (evaluateTaylorAt s G) = (G.map (evalZT z y)).eval s := by
  simp [evaluateTaylorAt, evalZT, Polynomial.eval_map]

/-- The common truncation evaluates to the single common denominator times
the actual (already translated and scaled) root polynomial. -/
theorem commonDenominatorTaylorTruncation_eval_eq
    (h k : Nat) (q : Polynomial F) (seq : Nat → Fin h → Polynomial F)
    (z y s : F) (g : Polynomial F) (hq : q.eval z ≠ 0)
    (hgdeg : g.natDegree ≤ k)
    (hseq : ∀ i : Fin (k + 1),
      evalZT z y (vectorPolynomial h (seq i.1)) *
          (q.eval z)⁻¹ ^ oddDenomExponent i.1 = g.coeff i.1) :
    evalZT z y
        (evaluateTaylorAt s
          (commonDenominatorTaylorTruncation h k q seq)) =
      q.eval z ^ oddDenomExponent k * g.eval s := by
  rw [evalZT_evaluateTaylorAt]
  rw [map_commonDenominatorTaylorTruncation h k q seq z y g hq hseq]
  rw [truncatePolynomial_eq_self_of_natDegree_le k g hgdeg]
  simp

/-- The polynomial `a + Z b` encoding one affine-line coordinate. -/
def affineCoordinatePolynomial (a b : F) : Polynomial F :=
  Polynomial.C a + Polynomial.X * Polynomial.C b

@[simp] theorem eval_affineCoordinatePolynomial (a b z : F) :
    (affineCoordinatePolynomial a b).eval z = a + z * b := by
  simp [affineCoordinatePolynomial]

/-- Difference between the universal coordinate value and the proposed
affine coordinate, reduced to the canonical representative modulo `Hbar`. -/
def alignmentRemainder (Hbar : Polynomial (Polynomial F))
    (Gx : Polynomial (Polynomial F)) (scale : Polynomial F) (a b : F) :
    Polynomial (Polynomial F) :=
  canonicalRemainder Hbar
    (Gx - Polynomial.C (scale * affineCoordinatePolynomial a b))

theorem eval_alignmentRemainder_eq_zero
    (Hbar Gx : Polynomial (Polynomial F)) (scale : Polynomial F)
    (a b z y : F)
    (hy : (specializeZ z Hbar).eval y = 0)
    (hGx : evalZT z y Gx = scale.eval z * (a + z * b)) :
    evalZT z y (alignmentRemainder Hbar Gx scale a b) = 0 := by
  change (specializeZ z
    (canonicalRemainder Hbar
      (Gx - Polynomial.C (scale * affineCoordinatePolynomial a b)))).eval y = 0
  rw [eval_specializeZ_canonicalRemainder_at_root z y Hbar _ hy]
  change evalZT z y Gx -
    (scale * affineCoordinatePolynomial a b).eval z = 0
  rw [hGx, Polynomial.eval_mul, eval_affineCoordinatePolynomial]
  ring

/-! ## Fixed resultant promotion -/

/-- A fixed-size resultant, chosen before specialization so mapping at `Z=z`
commutes even when a specialized degree drops. -/
def quotientResultant (H beta : Polynomial (Polynomial F)) : Polynomial F :=
  Polynomial.resultant H beta H.natDegree beta.natDegree

theorem quotientResultant_eval_eq_zero_of_common_root
    (H beta : Polynomial (Polynomial F)) (hHpos : 0 < H.natDegree)
    (z y : F) (hHroot : (specializeZ z H).eval y = 0)
    (hbetaRoot : (specializeZ z beta).eval y = 0) :
    (quotientResultant H beta).eval z = 0 := by
  let f := specializeZ z H
  let g := specializeZ z beta
  have hfdeg : f.natDegree ≤ H.natDegree := Polynomial.natDegree_map_le
  have hgdeg : g.natDegree ≤ beta.natDegree := Polynomial.natDegree_map_le
  obtain ⟨p, q, _hp, _hq, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hfdeg hgdeg
      (Or.inl hHpos.ne')
  have heval := congrArg (Polynomial.evalRingHom y) hbez
  have hfixed :
      Polynomial.resultant f g H.natDegree beta.natDegree = 0 := by
    simpa [f, g, hHroot, hbetaRoot] using heval.symm
  change (Polynomial.evalRingHom z)
    (Polynomial.resultant H beta H.natDegree beta.natDegree) = 0
  rw [← Polynomial.resultant_map_map]
  exact hfixed

/-- If `H` is an irreducible positive-degree branch and `beta` is its
strictly lower-degree canonical representative, vanishing of their universal
resultant forces `beta=0`.  The proof passes to `Frac(F[Z])`, where Gauss's
lemma preserves irreducibility and irreducibles generate prime ideals. -/
theorem alignmentRemainder_eq_zero_of_quotientResultant_eq_zero
    (H beta : Polynomial (Polynomial F))
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hbetaDegree : beta.natDegree < H.natDegree)
    (hresultant : quotientResultant H beta = 0) :
    beta = 0 := by
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  let f : Polynomial K := H.map φ
  let g : Polynomial K := beta.map φ
  have hφinj : Function.Injective φ :=
    IsFractionRing.injective (Polynomial F) K
  have hprim : H.IsPrimitive :=
    Irreducible.isPrimitive hHirr (Nat.ne_of_gt hHpos)
  have hfirr : Irreducible f := by
    exact (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := K) hprim).mp hHirr
  have hfdeg : f.natDegree = H.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφinj
  have hgdeg : g.natDegree = beta.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφinj
  have hresK : Polynomial.resultant f g = 0 := by
    change Polynomial.resultant f g f.natDegree g.natDegree = 0
    rw [hfdeg, hgdeg]
    change φ (quotientResultant H beta) = 0
    rw [hresultant, map_zero]
  have hnotcop : ¬ IsCoprime f g :=
    (Polynomial.resultant_eq_zero_iff.mp hresK).2
  have hfg : f ∣ g := hfirr.dvd_iff_not_isCoprime.mpr hnotcop
  by_contra hbeta
  have hg0 : g ≠ 0 := by
    intro hg
    apply hbeta
    exact hφinj (by simpa [g] using hg)
  have hle : f.natDegree ≤ g.natDegree :=
    Polynomial.natDegree_le_of_dvd hfg hg0
  rw [hfdeg, hgdeg] at hle
  omega

/-- Complete rich-coordinate promotion.  If the fixed resultant degree is
strictly below the number of rich seeds (in the target application both are
compared to `2^47`), common specialized roots force the canonical alignment
remainder to vanish universally. -/
theorem alignmentRemainder_eq_zero_of_many_common_roots
    {Seed : Type*} [DecidableEq Seed]
    (seeds : Finset Seed) (z : Seed → F)
    (hz : Set.InjOn z (seeds : Set Seed))
    (H beta : Polynomial (Polynomial F))
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hbetaDegree : beta.natDegree < H.natDegree)
    (hresultantDegree : (quotientResultant H beta).natDegree < seeds.card)
    (yAt : Seed → F)
    (hHroot : ∀ seed ∈ seeds,
      (specializeZ (z seed) H).eval (yAt seed) = 0)
    (hbetaRoot : ∀ seed ∈ seeds,
      (specializeZ (z seed) beta).eval (yAt seed) = 0) :
    beta = 0 := by
  apply alignmentRemainder_eq_zero_of_quotientResultant_eq_zero
    H beta hHirr hHpos hbetaDegree
  apply polynomial_eq_zero_of_many_evaluations seeds z hz
    (quotientResultant H beta) hresultantDegree
  intro seed hseed
  exact quotientResultant_eval_eq_zero_of_common_root H beta hHpos
    (z seed) (yAt seed) (hHroot seed hseed) (hbetaRoot seed hseed)

/-! ## Coefficientwise `k+1` alignment -/

/-- Interpolation over the domain `F[Z]` at constant points `C x`.  This is
the coefficient-level Vandermonde step used after each rich coordinate has
zero canonical remainder. -/
theorem polynomialOverZ_eq_of_many_X_evaluations
    {Index : Type*} [Fintype Index]
    (x : Index → F) (hx : Function.Injective x)
    (A B : Polynomial (Polynomial F))
    (hdegree : max A.natDegree B.natDegree < Fintype.card Index)
    (heval : ∀ i,
      A.eval (Polynomial.C (x i)) = B.eval (Polynomial.C (x i))) :
    A = B := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq A B
    (f := fun i => Polynomial.C (x i))
  · intro i j hij
    exact hx (Polynomial.C_injective hij)
  · exact heval
  · exact hdegree

/-- Reassemble coefficientwise polynomial identities in the quotient/root
variable.  `B` is viewed as `F[Z][X][T]`, with `T` outermost. -/
theorem trivariate_eq_zero_of_coeffwise_many_X_evaluations
    {Index : Type*} [Fintype Index]
    (x : Index → F) (hx : Function.Injective x)
    (B : Polynomial (Polynomial (Polynomial F)))
    (hdegree : ∀ j, (B.coeff j).natDegree < Fintype.card Index)
    (hvanish : ∀ j i,
      (B.coeff j).eval (Polynomial.C (x i)) = 0) :
    B = 0 := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_zero]
  apply polynomialOverZ_eq_of_many_X_evaluations x hx (B.coeff j) 0
  · simpa using hdegree j
  · intro i
    simpa using hvanish j i

/-- Cancellation after quotient rigidity has identified the common Taylor
polynomial with a scaled affine combination. -/
theorem cancel_common_scale_polynomial_alignment
    (qz Wz : F) (E : Nat) (hq : qz ≠ 0) (hW : Wz ≠ 0)
    (p p₀ p₁ : Polynomial F) (z : F)
    (halign : Polynomial.C (qz ^ E * Wz) * p =
      Polynomial.C (qz ^ E * Wz) *
        (p₀ + Polynomial.C z * p₁)) :
    p = p₀ + Polynomial.C z * p₁ := by
  apply mul_left_cancel₀
  · simp [hq, hW]
  · exact halign

/-- Pointwise cancellation on a retained seed set; this is the final bridge
to `SelectedPolynomialAlignment` once the exceptional `q` and `W` roots have
been filtered out. -/
theorem selected_polynomials_aligned_after_cancellation
    {Seed : Type*} (seeds : Set Seed) (z qz Wz : Seed → F) (E : Nat)
    (selected : Seed → Polynomial F) (p₀ p₁ : Polynomial F)
    (hq : ∀ seed ∈ seeds, qz seed ≠ 0)
    (hW : ∀ seed ∈ seeds, Wz seed ≠ 0)
    (halign : ∀ seed ∈ seeds,
      Polynomial.C ((qz seed) ^ E * Wz seed) * selected seed =
        Polynomial.C ((qz seed) ^ E * Wz seed) *
          (p₀ + Polynomial.C (z seed) * p₁)) :
    ∀ seed ∈ seeds,
      selected seed = p₀ + Polynomial.C (z seed) * p₁ := by
  intro seed hseed
  exact cancel_common_scale_polynomial_alignment
    (qz seed) (Wz seed) E (hq seed hseed) (hW seed hseed)
    (selected seed) p₀ p₁ (z seed) (halign seed hseed)

/-! ## Concrete 53.14 branch assembly -/

open FactorThreshold5314 AgreementIncidence5314

/-- Removing the entire explicit exceptional set from a second-factor branch
leaves more than `2^50` seeds and hence more than `131071` rich coordinates. -/
theorem target5314_rich_coordinates_after_exception_filtering
    {Seed : Type*} [DecidableEq Seed]
    (branch exceptions : Finset Seed)
    (hexceptions : exceptions ⊆ branch)
    (support : Seed → Finset IRSProfile.Index)
    (hbranch : branchThreshold < branch.card)
    (hexceptionCard : exceptions.card < 2 ^ 45)
    (hsupport : ∀ seed ∈ branch \ exceptions,
      196592 ≤ (support seed).card) :
    131071 <
      (richCoordinates (branch \ exceptions) support (2 ^ 47)).card := by
  apply target5314_many_rich_coordinates (branch \ exceptions) support hsupport
  rw [Finset.card_sdiff hexceptions]
  exact branch_survives_exception_budget hbranch hexceptionCard

/-- Concrete rich-fiber/resultant/reassembly core.  All construction-specific
degree estimates are explicit: each fixed resultant is below `2^47`, and each
coefficient polynomial in `X` has degree at most `131071`. -/
theorem target5314_rich_resultants_force_global_coefficient_identity
    {Seed : Type*} [DecidableEq Seed]
    (branch exceptions : Finset Seed)
    (hexceptions : exceptions ⊆ branch)
    (support : Seed → Finset IRSProfile.Index)
    (hbranch : branchThreshold < branch.card)
    (hexceptionCard : exceptions.card < 2 ^ 45)
    (hsupport : ∀ seed ∈ branch \ exceptions,
      196592 ≤ (support seed).card)
    (z : Seed → IRSProfile.Field)
    (hz : Set.InjOn z ((branch \ exceptions : Finset Seed) : Set Seed))
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (yAt : Seed → IRSProfile.Field)
    (hHroot : ∀ seed ∈ branch \ exceptions,
      (specializeZ (z seed) H).eval (yAt seed) = 0)
    (beta : IRSProfile.Index → Polynomial (Polynomial IRSProfile.Field))
    (hbetaDegree : ∀ i, (beta i).natDegree < H.natDegree)
    (hresultantDegree : ∀ i,
      (quotientResultant H (beta i)).natDegree < 2 ^ 47)
    (hbetaRoot : ∀ i seed,
      i ∈ richCoordinates (branch \ exceptions) support (2 ^ 47) →
      seed ∈ branch \ exceptions → i ∈ support seed →
      (specializeZ (z seed) (beta i)).eval (yAt seed) = 0)
    (B : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hBdegree : ∀ j, (B.coeff j).natDegree ≤ 131071)
    (hBvanish : ∀ i,
      i ∈ richCoordinates (branch \ exceptions) support (2 ^ 47) →
      beta i = 0 → ∀ j,
        (B.coeff j).eval (Polynomial.C (IRSProfile.domain i)) = 0) :
    B = 0 := by
  classical
  let good := branch \ exceptions
  let rich := richCoordinates good support (2 ^ 47)
  have hrichCard : 131071 < rich.card := by
    dsimp only [rich, good]
    exact target5314_rich_coordinates_after_exception_filtering
      branch exceptions hexceptions support hbranch hexceptionCard hsupport
  have hbetaZero : ∀ i ∈ rich, beta i = 0 := by
    intro i hi
    let fiber := good.filter fun seed => i ∈ support seed
    have hfiberCard : 2 ^ 47 < fiber.card := by
      simpa [fiber, rich, richCoordinates, incidence] using hi
    apply alignmentRemainder_eq_zero_of_many_common_roots
      fiber z (hz.mono (by
        intro seed hseed
        exact (Finset.mem_filter.mp hseed).1))
      H (beta i) hHirr hHpos (hbetaDegree i)
      ((hresultantDegree i).trans hfiberCard) yAt
    · intro seed hseed
      exact hHroot seed (Finset.mem_filter.mp hseed).1
    · intro seed hseed
      have hs := Finset.mem_filter.mp hseed
      exact hbetaRoot i seed (by simpa [rich] using hi) hs.1 hs.2
  let RichIndex := {i : IRSProfile.Index // i ∈ rich}
  have hx : Function.Injective (fun i : RichIndex => IRSProfile.domain i.1) :=
    fun _ _ h => Subtype.ext (IRSProfile.domain.injective h)
  apply trivariate_eq_zero_of_coeffwise_many_X_evaluations
    (F := IRSProfile.Field) (Index := RichIndex)
    (fun i => IRSProfile.domain i.1) hx B
  · intro j
    rw [Fintype.card_coe]
    exact (hBdegree j).trans_lt hrichCard
  · intro j i
    exact hBvanish i.1 (by simpa [rich] using i.2)
      (hbetaZero i.1 i.2) j

end

end ProximityPrize.SubmissionLower.FiniteTaylorEvaluatedBridge
