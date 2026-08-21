import ProximityPrize.SubmissionLower.BCHKSStagedSelection
import ProximityPrize.SubmissionLower.BCHKSResultantDegree
import ProximityPrize.SubmissionLower.BCHKSRationalRootVanishing
import ProximityPrize.SubmissionLower.BCHKSRationalRootBridge
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSHenselWeight

namespace ProximityPrize.SubmissionLower

open Polynomial
open Polynomial.Bivariate
open RationalFunctions

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- Two-stage selection which retains the actual cost of each second-stage
factor.  Unlike the older selector, this theorem does not first replace the
inner sum by `pairCost R * degree R`; that is the point at which the repeated
global `Y/Z` cap used to create the coarse square charge. -/
theorem exists_staged_weighted_selection_by_pair
    {σ ρ η : Type*} [DecidableEq σ] [DecidableEq ρ] [DecidableEq η]
    (S : Finset σ) (Rs : Finset ρ) (Hs : ρ → Finset η)
    (bad : ρ → Nat) (pairCost : ρ → η → Nat) (e : Nat)
    (RelR : σ → ρ → Prop) [DecidableRel RelR]
    (RelH : σ → ρ → η → Prop) [∀ r, DecidableRel (fun z h => RelH z r h)]
    (Bad : ρ → Finset σ)
    (hRcover : ∀ z ∈ S, ∃ r ∈ Rs, RelR z r)
    (hglobal :
      (∑ r ∈ Rs, ((∑ h ∈ Hs r, (pairCost r h + e)) + bad r)) < S.card)
    (hBad : ∀ r ∈ Rs, ((S.filter fun z => RelR z r) ∩ Bad r).card ≤ bad r)
    (hHcover : ∀ r ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z r) \ Bad r,
      ∃ h ∈ Hs r, RelH z r h) :
    ∃ r ∈ Rs, ∃ h ∈ Hs r, ∃ T : Finset σ,
      T ⊆ S ∧
      (∀ z ∈ T, z ∉ Bad r) ∧
      (∀ z ∈ T, RelR z r ∧ RelH z r h) ∧
      pairCost r h + e < T.card := by
  classical
  let capR : ρ → Nat := fun r => (∑ h ∈ Hs r, (pairCost r h + e)) + bad r
  obtain ⟨r, hr, hrfiber⟩ :=
    exists_rel_fiber_gt_capacity S Rs RelR capR hRcover
      (by simpa [capR] using hglobal)
  let U := S.filter fun z => RelR z r
  have hbadU : (U ∩ Bad r).card ≤ bad r := by simpa [U] using hBad r hr
  have hUgood : (∑ h ∈ Hs r, (pairCost r h + e)) < (U \ Bad r).card := by
    rw [Finset.card_sdiff]
    apply Nat.lt_sub_of_add_lt
    have hbadd : (∑ h ∈ Hs r, (pairCost r h + e)) + (Bad r ∩ U).card ≤
        (∑ h ∈ Hs r, (pairCost r h + e)) + bad r := by
      apply Nat.add_le_add_left
      simpa [Finset.inter_comm] using hbadU
    exact hbadd.trans_lt (by simpa [capR, U] using hrfiber)
  obtain ⟨h, hh, hhfiber⟩ :=
    exists_rel_fiber_gt_capacity (U \ Bad r) (Hs r)
      (fun z h => RelH z r h) (fun h => pairCost r h + e)
      (hHcover r hr) hUgood
  let T := (U \ Bad r).filter fun z => RelH z r h
  refine ⟨r, hr, h, hh, T, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).1
  · intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hz'.1).1).2, hz'.2⟩
  · simpa [T] using hhfiber

/-- Normalized-factor version of `exists_staged_weighted_selection_by_pair`.
This is the concrete selection seam needed by a multigraded Hensel/resultant
bound: its cost may depend on both the outer factor `R` and the specialized
factor `H`. -/
theorem exists_concrete_staged_factor_selection_by_pair
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (S : Finset F) (P : F → Polynomial F)
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x₀ : Polynomial (Polynomial (Polynomial F)) → F)
    (Bad : Polynomial (Polynomial (Polynomial F)) → Finset F)
    (badCap : Polynomial (Polynomial (Polynomial F)) → Nat)
    (pairCost : Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) → Nat)
    (e : Nat)
    (hQeval : ∀ z ∈ S, triEval Q z (P z) = 0)
    (hQz : ∀ z ∈ S, triSpecializeZ Q z ≠ 0)
    (hBadCap : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → (Bad R).card ≤ badCap R)
    (hsecond : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      0 < R.natDegree → ∀ z ∈ S \ Bad R,
        biSpecializeZ (triSpecializeX R (x₀ R)) z ≠ 0)
    (hglobal :
      (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun R => 0 < R.natDegree),
        (((∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R (x₀ R))).toFinset.filter
              (fun H => 0 < H.natDegree), (pairCost R H + e))) + badCap R)) < S.card) :
    ∃ R H T,
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < R.natDegree ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R (x₀ R)) ∧
      0 < H.natDegree ∧ T ⊆ S ∧ (∀ z ∈ T, z ∉ Bad R) ∧
      (∀ z ∈ T, triEval R z (P z) = 0 ∧
        biEval H (Polynomial.eval (x₀ R) (P z)) z = 0) ∧
      pairCost R H + e < T.card := by
  classical
  let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    fun R => 0 < R.natDegree
  let Hs : Polynomial (Polynomial (Polynomial F)) →
      Finset (Polynomial (Polynomial F)) := fun R =>
    (UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R (x₀ R))).toFinset.filter fun H => 0 < H.natDegree
  let RelR : F → Polynomial (Polynomial (Polynomial F)) → Prop :=
    fun z R => triEval R z (P z) = 0
  let RelH : F → Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) → Prop :=
    fun z R H => biEval H (Polynomial.eval (x₀ R) (P z)) z = 0
  have hRcover : ∀ z ∈ S, ∃ R ∈ Rs, RelR z R := by
    intro z hz
    obtain ⟨R, hRQ, hRpos, hzero⟩ :=
      exists_positive_normalizedFactor_triEval_eq_zero Q z (P z)
        (hQz z hz) (hQeval z hz)
    exact ⟨R, by simp [Rs, hRQ, hRpos], hzero⟩
  have hHcover : ∀ R ∈ Rs, ∀ z ∈ (S.filter fun z => RelR z R) \ Bad R,
      ∃ H ∈ Hs R, RelH z R H := by
    intro R hR z hz
    have hRm := Finset.mem_filter.mp hR
    have hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
      simpa [Rs] using hRm.1
    have hzS : z ∈ S := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
    have hzgood : z ∈ S \ Bad R :=
      Finset.mem_sdiff.mpr ⟨hzS, (Finset.mem_sdiff.mp hz).2⟩
    have hRzero : RelR z R :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
    have hpoint : biEval (triSpecializeX R (x₀ R))
        (Polynomial.eval (x₀ R) (P z)) z = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX, hRzero]
      simp
    obtain ⟨H, hHR, hHpos, hHzero⟩ :=
      exists_positive_normalizedFactor_biEval_eq_zero
        (triSpecializeX R (x₀ R)) z (Polynomial.eval (x₀ R) (P z))
        (hsecond R hRQ hRm.2 z hzgood) hpoint
    exact ⟨H, by simp [Hs, hHR, hHpos], hHzero⟩
  have hBad : ∀ R ∈ Rs,
      ((S.filter fun z => RelR z R) ∩ Bad R).card ≤ badCap R := by
    intro R hR
    apply (Finset.card_le_card Finset.inter_subset_right).trans
    have hm := Finset.mem_filter.mp hR
    exact hBadCap R (by simpa [Rs] using hm.1) hm.2
  obtain ⟨R, hRs, H, hHs, T, hTS, hTbad, hrel, hmargin⟩ :=
    exists_staged_weighted_selection_by_pair S Rs Hs badCap pairCost e
      RelR RelH Bad hRcover (by simpa [Rs, Hs] using hglobal)
      hBad hHcover
  have hRm := Finset.mem_filter.mp hRs
  have hHm := Finset.mem_filter.mp hHs
  exact ⟨R, H, T, by simpa [Rs] using hRm.1, hRm.2,
    by simpa [Hs] using hHm.1, hHm.2, hTS, hTbad, hrel, hmargin⟩

namespace SecondStageCapacity

variable {F : Type} [Field F]

/-- Primitive (not necessarily monic) descent for a vanishing bivariate
resultant.  This is what lets the refined root count work with the original
specialization factor instead of its degree-inflating monicization. -/
theorem irreducible_dvd_of_resultant_eq_zero_of_isPrimitive
    (B H : F[X][Y]) (hHprimitive : H.IsPrimitive)
    (hHirreducible : Irreducible H)
    (hres : Polynomial.resultant B H = 0) : H ∣ B := by
  classical
  let K := FractionRing F[X]
  let f : F[X] →+* K := algebraMap F[X] K
  have hf : Function.Injective f := IsFractionRing.injective F[X] K
  have hBdeg : (B.map f).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf B
  have hHdeg : (H.map f).natDegree = H.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf H
  have hresFixed :
      Polynomial.resultant (B.map f) (H.map f) B.natDegree H.natDegree = 0 := by
    rw [Polynomial.resultant_map_map, hres]
    exact map_zero f
  have hresK : Polynomial.resultant (B.map f) (H.map f) = 0 := by
    simpa only [hBdeg, hHdeg] using hresFixed
  have hnotCoprime : ¬ IsCoprime (B.map f) (H.map f) :=
    (Polynomial.resultant_eq_zero_iff.mp hresK).2
  have hHirreducibleK : Irreducible (H.map f) :=
    hHprimitive.irreducible_iff_irreducible_map_fraction_map.mp hHirreducible
  have hdvdK : H.map f ∣ B.map f :=
    (Irreducible.dvd_iff_not_isCoprime hHirreducibleK).2 fun hc =>
      hnotCoprime hc.symm
  exact hHprimitive.dvd_of_fraction_map_dvd_fraction_map hdvdK

/-- Raw-coordinate bivariate root count.  It avoids monicization and hence
retains the actual coefficient-variable degrees of both polynomials. -/
theorem irreducible_dvd_of_many_bivariate_common_roots_primitive
    (B H : F[X][Y]) (S : Finset F) (t : F → F)
    (hHprimitive : H.IsPrimitive) (hHirreducible : Irreducible H)
    (hHpos : 0 < H.natDegree)
    (hmany : H.natDegree * degreeX B + B.natDegree * degreeX H < S.card)
    (hroots : ∀ z ∈ S,
      (B.map (Polynomial.evalRingHom z)).eval (t z) = 0 ∧
      (H.map (Polynomial.evalRingHom z)).eval (t z) = 0) :
    H ∣ B := by
  let Res : F[X] := Polynomial.resultant B H
  have hReval : ∀ z ∈ S, Res.eval z = 0 := by
    intro z hz
    dsimp [Res]
    exact bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
      B H z (t z) (by omega) (hroots z hz).1 (hroots z hz).2
  have hRdeg : Res.natDegree ≤
      H.natDegree * degreeX B + B.natDegree * degreeX H := by
    dsimp [Res]
    exact bivariate_resultant_natDegree_le_of_declared_Y_degrees
      B H B.natDegree H.natDegree rfl rfl
  have hRzero : Res = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Res S hReval
      (hRdeg.trans_lt hmany)
  apply irreducible_dvd_of_resultant_eq_zero_of_isPrimitive B H
    hHprimitive hHirreducible
  simpa [Res] using hRzero

/-- Finite-type form of the primitive raw-coordinate root count. -/
theorem irreducible_dvd_of_many_bivariate_common_roots_primitive_fintype
    {ι : Type*} [Fintype ι]
    (B H : F[X][Y]) (z y : ι → F) (hzInj : Function.Injective z)
    (hHprimitive : H.IsPrimitive) (hHirreducible : Irreducible H)
    (hHpos : 0 < H.natDegree)
    (hmany : H.natDegree * degreeX B + B.natDegree * degreeX H <
      Fintype.card ι)
    (hroots : ∀ i,
      (B.map (Polynomial.evalRingHom (z i))).eval (y i) = 0 ∧
      (H.map (Polynomial.evalRingHom (z i))).eval (y i) = 0) :
    H ∣ B := by
  let Res : F[X] := Polynomial.resultant B H
  have hReval : ∀ i, Res.eval (z i) = 0 := by
    intro i
    dsimp [Res]
    exact bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
      B H (z i) (y i) (by omega) (hroots i).1 (hroots i).2
  have hRdeg : Res.natDegree ≤
      H.natDegree * degreeX B + B.natDegree * degreeX H := by
    dsimp [Res]
    exact bivariate_resultant_natDegree_le_of_declared_Y_degrees
      B H B.natDegree H.natDegree rfl rfl
  have hRzero : Res = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      Res hzInj hReval (hRdeg.trans_lt hmany)
  apply irreducible_dvd_of_resultant_eq_zero_of_isPrimitive B H
    hHprimitive hHirreducible
  simpa [Res] using hRzero

/-- Return from the integral monicized coordinate `T = W·Y` to the original
root coordinate. -/
noncomputable def rawRootCoordinate (H P : F[X][Y]) : F[X][Y] :=
  P.comp (Polynomial.C H.leadingCoeff * Polynomial.X)

theorem evalEval_rawRootCoordinate (H P : F[X][Y]) (z y : F) :
    Polynomial.evalEval z y (rawRootCoordinate H P) =
      Polynomial.evalEval z (H.leadingCoeff.eval z * y) P := by
  unfold rawRootCoordinate Polynomial.evalEval
  rw [Polynomial.eval_comp]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval_add]
      rw [hP, hQ]
  | monomial n a =>
      simp [Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_pow]

/-- Exact weighted-support control of the raw-coordinate numerator.  Scaling
the root variable by `W` charges the coefficient of `Y^i` exactly
`i * deg_Z(W)`, with no global total-degree replacement. -/
theorem degreeX_rawRootCoordinate_le_weightedSupport
    (H P : F[X][Y]) :
    degreeX (rawRootCoordinate H P) ≤
      WeightedFactorCaps.weightedSupportDegree P H.leadingCoeff.natDegree := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro i hi
  have hraw : (rawRootCoordinate H P).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  rw [rawRootCoordinate, Polynomial.comp_C_mul_X_coeff] at hraw ⊢
  have hPi : P.coeff i ≠ 0 := left_ne_zero_of_mul hraw
  calc
    (P.coeff i * H.leadingCoeff ^ i).natDegree ≤
        (P.coeff i).natDegree + (H.leadingCoeff ^ i).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (P.coeff i).natDegree + i * H.leadingCoeff.natDegree := by
      exact Nat.add_le_add_left Polynomial.natDegree_pow_le _
    _ ≤ WeightedFactorCaps.weightedSupportDegree P H.leadingCoeff.natDegree :=
      by simpa [Nat.mul_comm] using
        WeightedFactorCaps.coeffWeight_le_of_ne P H.leadingCoeff.natDegree i hPi

/-- Raw-coordinate vanishing criterion for a regular function-field element.
The hypotheses expose precisely the bidegrees that the refined Hensel
numerator induction must supply. -/
theorem embedding_eq_zero_of_many_raw_roots
    {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H)
    (S : Finset F) (y : F → F)
    (hHroot : ∀ z ∈ S, Polynomial.evalEval z (y z) H = 0)
    (hβroot : ∀ z, ∀ hz : z ∈ S,
      piZ z (rationalRootOfPair H hH z (y z) (hHroot z hz)) β = 0)
    (hmany :
      H.natDegree * degreeX
          (rawRootCoordinate H (canonicalRepOf𝒪 hH β)) +
        (rawRootCoordinate H (canonicalRepOf𝒪 hH β)).natDegree * degreeX H <
          S.card) :
    embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let P : F[X][Y] := canonicalRepOf𝒪 hH β
  let B : F[X][Y] := rawRootCoordinate H P
  have hroots : ∀ z ∈ S,
      (B.map (Polynomial.evalRingHom z)).eval (y z) = 0 ∧
      (H.map (Polynomial.evalRingHom z)).eval (y z) = 0 := by
    intro z hz
    have hpi := hβroot z hz
    rw [piZ_eq_eval_canonicalRepOf𝒪 hH] at hpi
    constructor
    · rw [Polynomial.map_evalRingHom_eval]
      change Polynomial.evalEval z (y z) B = 0
      rw [show B = rawRootCoordinate H P from rfl,
        evalEval_rawRootCoordinate]
      simpa [P, Polynomial.evalEval, Polynomial.eval_mul] using hpi
    · rw [Polynomial.map_evalRingHom_eval]
      exact hHroot z hz
  have hBdvd : H ∣ B := by
    apply irreducible_dvd_of_many_bivariate_common_roots_primitive
      B H S y ((Fact.out : Irreducible H).isPrimitive (Nat.ne_of_gt hH))
      (Fact.out : Irreducible H)
      hH
    · simpa [B, P] using hmany
    · exact hroots
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hscaleDeg :
      (Polynomial.C H.leadingCoeff * (Polynomial.X : F[X][Y])).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hWne]
    simp
  have hBdeg : B.natDegree = P.natDegree := by
    dsimp [B, rawRootCoordinate]
    rw [Polynomial.natDegree_comp, hscaleDeg, Nat.mul_one]
  have hPlt : P.natDegree < H.natDegree := by
    exact canonicalRepOf𝒪_natDegree_lt_H hH β
  have hBzero : B = 0 := by
    by_contra hBne
    exact Polynomial.not_dvd_of_natDegree_lt hBne (by simpa [hBdeg] using hPlt) hBdvd
  have hPzero : P = 0 := by
    have hcomp : P.comp (Polynomial.C H.leadingCoeff * Polynomial.X) = 0 := by
      simpa [B, rawRootCoordinate] using hBzero
    rcases Polynomial.comp_eq_zero_iff.mp hcomp with hp | hp
    · exact hp
    · exfalso
      have hconst := congrArg Polynomial.natDegree hp.2
      rw [hscaleDeg] at hconst
      simp at hconst
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H
    (Ideal.Quotient.mk (Ideal.span {monicize H}) P : 𝒪 H) = 0
  rw [hPzero]
  simp

/-- Usable weighted-support form of the raw-coordinate criterion. -/
theorem embedding_eq_zero_of_many_raw_roots_weightedSupport
    {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H)
    (S : Finset F) (y : F → F)
    (hHroot : ∀ z ∈ S, Polynomial.evalEval z (y z) H = 0)
    (hβroot : ∀ z, ∀ hz : z ∈ S,
      piZ z (rationalRootOfPair H hH z (y z) (hHroot z hz)) β = 0)
    (hmany :
      H.natDegree * WeightedFactorCaps.weightedSupportDegree
          (canonicalRepOf𝒪 hH β) H.leadingCoeff.natDegree +
        (canonicalRepOf𝒪 hH β).natDegree * degreeX H < S.card) :
    embeddingOf𝒪Into𝕃 H β = 0 := by
  apply embedding_eq_zero_of_many_raw_roots hH β S y hHroot hβroot
  have hZ := degreeX_rawRootCoordinate_le_weightedSupport H
    (canonicalRepOf𝒪 hH β)
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hscaleDeg :
      (Polynomial.C H.leadingCoeff * (Polynomial.X : F[X][Y])).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hWne]
    simp
  have hY : (rawRootCoordinate H (canonicalRepOf𝒪 hH β)).natDegree =
      (canonicalRepOf𝒪 hH β).natDegree := by
    unfold rawRootCoordinate
    rw [Polynomial.natDegree_comp, hscaleDeg, Nat.mul_one]
  exact lt_of_le_of_lt
    (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hZ)
      (by rw [hY])) hmany

/-- Multigraded replacement for the scalar-weight rational-root bound.  It
keeps the two Sylvester contributions separate:

`degY(H) * degZ(β) + degY(β) * degZ(monicize H)`.

This is the algebraic interface needed to exploit complementary factor
degrees; the old `regularWeight * H.natDegree` bound erases this split. -/
theorem embedding_eq_zero_of_many_rational_roots_bidegree
    {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H)
    (BZ BY HZ : Nat)
    (hβZ : Polynomial.Bivariate.degreeX (canonicalRepOf𝒪 hH β) ≤ BZ)
    (hβY : (canonicalRepOf𝒪 hH β).natDegree ≤ BY)
    (hHZ : Polynomial.Bivariate.degreeX (monicize H) ≤ HZ)
    (hncard : BZ * H.natDegree + BY * HZ <
      Set.ncard (rationalVanishingSet β)) :
    embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  let q : F[X][Y] := monicize H
  let Res : F[X] := Polynomial.resultant p q
  have hqdeg : q.natDegree = H.natDegree := by
    simpa [q] using natDegree_monicize (H := H) hH
  have hResdeg : Res.natDegree ≤ BZ * H.natDegree + BY * HZ := by
    calc
      Res.natDegree ≤ H.natDegree * Polynomial.Bivariate.degreeX p +
          p.natDegree * Polynomial.Bivariate.degreeX q := by
        dsimp [Res]
        exact bivariate_resultant_natDegree_le_of_declared_Y_degrees
          p q p.natDegree H.natDegree rfl hqdeg
      _ ≤ H.natDegree * BZ + BY * HZ := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left H.natDegree (by simpa [p] using hβZ))
          (Nat.mul_le_mul hβY hHZ)
      _ = BZ * H.natDegree + BY * HZ := by ring
  have hReszero : Res = 0 := by
    apply poly_eq_zero_of_ncard_gt_bound_of_subset_roots
      (S := rationalVanishingSet β)
      (N := BZ * H.natDegree + BY * HZ)
    · dsimp [Res, p, q]
      exact rationalVanishingSet_subset_resultant_roots hH β
    · exact hResdeg
    · exact hncard
  apply embedding_eq_zero_of_resultant_zero hH β
  simpa [Res, p, q] using hReszero

/-- Exact additivity of bivariate total degree over a finite product of
nonzero factors. -/
theorem totalDegree_finset_prod
    (s : Finset (Polynomial (Polynomial F)))
    (hzero : ∀ H ∈ s, H ≠ 0) :
    Polynomial.Bivariate.totalDegree (∏ H ∈ s, H) =
      ∑ H ∈ s, Polynomial.Bivariate.totalDegree H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      unfold Polynomial.Bivariate.totalDegree
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro i hi
      cases i with
      | zero => simp
      | succ i =>
          have hz : (1 : Polynomial (Polynomial F)).coeff (i + 1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by simp)
          exact ((Polynomial.mem_support_iff.mp hi) hz).elim
  | @insert H s hHs ih =>
      have hH : H ≠ 0 := hzero H (by simp)
      have hs : ∏ A ∈ s, A ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro A hA
        exact hzero A (by simp [hA])
      rw [Finset.prod_insert hHs, Finset.sum_insert hHs,
        Polynomial.Bivariate.totalDegree_mul (F := F) (f := H)
          (g := ∏ A ∈ s, A) hH hs,
        ih (fun A hA => hzero A (by simp [hA]))]

/-- Removing multiplicities from the normalized factorization can only lower
the sum of bivariate total degrees. -/
theorem normalizedFactors_toFinset_sum_totalDegree_le
    [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial F)) (hQ : Q ≠ 0) :
    ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
        Polynomial.Bivariate.totalDegree H ≤
      Polynomial.Bivariate.totalDegree Q := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  let s := M.toFinset
  have ha := UniqueFactorizationMonoid.prod_normalizedFactors hQ
  have hM0 : M.prod ≠ 0 := fun h => hQ (ha.eq_zero_iff.mp h)
  have hs0 : ∀ H ∈ s, H ≠ 0 := by
    intro H hH
    exact UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hH)
  have hdvd : s.prod id ∣ M.prod := by
    apply Multiset.prod_dvd_prod_of_le
    simpa [s, M, Multiset.toFinset_val] using (Multiset.dedup_le M)
  have hprod0 : s.prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro H hH
    exact hs0 H hH
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0)
      (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul (F := F) (f := A) (g := C) hA hC]
    exact Nat.le_add_right _ _
  calc
    ∑ H ∈ s, Polynomial.Bivariate.totalDegree H =
        Polynomial.Bivariate.totalDegree (s.prod id) := by
      simpa only [id_eq] using
        (totalDegree_finset_prod s hs0).symm
    _ ≤ Polynomial.Bivariate.totalDegree M.prod :=
      totalDegree_le_of_dvd hprod0 hM0 hdvd
    _ ≤ Polynomial.Bivariate.totalDegree Q :=
      totalDegree_le_of_dvd hM0 hQ ha.dvd

/-- Local second-stage accounting: if every selected specialization factor
has outer degree at most `M`, charging it by its own total degree costs only
`dR * M * D`, not `dR^2 * D`. -/
theorem sum_pair_cost_le_of_local_total_degrees
    {η : Type*} [DecidableEq η] (Hs : Finset η)
    (deg total : η → Nat) (C dR D M : Nat)
    (hdeg : ∀ H ∈ Hs, deg H ≤ M)
    (htotal : (∑ H ∈ Hs, total H) ≤ D) :
    (∑ H ∈ Hs, C * dR * total H * deg H) ≤ C * dR * D * M := by
  calc
    (∑ H ∈ Hs, C * dR * total H * deg H) ≤
        ∑ H ∈ Hs, C * dR * total H * M := by
      apply Finset.sum_le_sum
      intro H hH
      exact Nat.mul_le_mul_left (C * dR * total H) (hdeg H hH)
    _ = ∑ H ∈ Hs, (C * dR * M) * total H := by
      apply Finset.sum_congr rfl
      intro H hH
      ring
    _ = (C * dR * M) * (∑ H ∈ Hs, total H) := by
      rw [Finset.mul_sum]
    _ = C * dR * (∑ H ∈ Hs, total H) * M := by ring
    _ ≤ C * dR * D * M := by
      exact Nat.mul_le_mul_right M (Nat.mul_le_mul_left (C * dR) htotal)

/-- Normalized-factor instantiation of the local second-stage estimate.  The
`e` overhead is paid once per distinct positive factor and their number is
bounded by the outer degree of the specialization. -/
theorem normalized_second_stage_pair_sum_le
    [DecidableEq F] [NormalizationMonoid F]
    (RX : Polynomial (Polynomial F)) (hRX : RX ≠ 0)
    (C dR D M e : Nat)
    (hRXdeg : RX.natDegree ≤ dR)
    (hRXtotal : Polynomial.Bivariate.totalDegree RX ≤ D)
    (hmax : ∀ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
      (fun H => 0 < H.natDegree), H.natDegree ≤ M) :
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
        (fun H => 0 < H.natDegree),
      (C * dR * Polynomial.Bivariate.totalDegree H * H.natDegree + e)) ≤
        C * dR * D * M + e * dR := by
  classical
  let Hs := (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
    (fun H => 0 < H.natDegree)
  have htotal : (∑ H ∈ Hs, Polynomial.Bivariate.totalDegree H) ≤ D := by
    calc
      (∑ H ∈ Hs, Polynomial.Bivariate.totalDegree H) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset,
            Polynomial.Bivariate.totalDegree H := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Polynomial.Bivariate.totalDegree RX :=
        normalizedFactors_toFinset_sum_totalDegree_le RX hRX
      _ ≤ D := hRXtotal
  have hdegsum : (∑ H ∈ Hs, H.natDegree) ≤ dR := by
    calc
      (∑ H ∈ Hs, H.natDegree) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset,
            H.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ RX.natDegree := normalizedFactors_toFinset_sum_natDegree_le RX hRX
      _ ≤ dR := hRXdeg
  have hcard : Hs.card ≤ dR := by
    calc
      Hs.card = ∑ H ∈ Hs, 1 := by simp
      _ ≤ ∑ H ∈ Hs, H.natDegree := by
        apply Finset.sum_le_sum
        intro H hH
        exact (Finset.mem_filter.mp hH).2
      _ ≤ dR := hdegsum
  have hmain := sum_pair_cost_le_of_local_total_degrees Hs
    Polynomial.natDegree Polynomial.Bivariate.totalDegree C dR D M
    (by
      intro H hH
      exact hmax H (by simpa [Hs] using hH)) htotal
  calc
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
        (fun H => 0 < H.natDegree),
      (C * dR * Polynomial.Bivariate.totalDegree H * H.natDegree + e)) =
        (∑ H ∈ Hs,
          C * dR * Polynomial.Bivariate.totalDegree H * H.natDegree) +
            Hs.card * e := by
      dsimp [Hs]
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ C * dR * D * M + e * dR := by
      exact Nat.add_le_add hmain (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right e hcard)

/-- Pair unit consumed by the raw bidegree resultant. -/
noncomputable def rawPairUnit (dR D : Nat) (H : Polynomial (Polynomial F)) : Nat :=
  H.natDegree * D + dR * Polynomial.Bivariate.degreeX H

private theorem degreeX_le_totalDegree (P : Polynomial (Polynomial F)) :
    Polynomial.Bivariate.degreeX P ≤ Polynomial.Bivariate.totalDegree P := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  exact (Nat.le_add_right _ i).trans
    (Polynomial.Bivariate.coeff_totalDegree_le P hi)

/-- The complete raw second-stage sum is linear in the selected outer degree.
Both components of `rawPairUnit` are additive over normalized factors. -/
theorem normalized_raw_pair_sum_le
    [DecidableEq F] [NormalizationMonoid F]
    (RX : Polynomial (Polynomial F)) (hRX : RX ≠ 0)
    (C dR D e : Nat)
    (hRXdeg : RX.natDegree ≤ dR)
    (hRXtotal : Polynomial.Bivariate.totalDegree RX ≤ D) :
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
        (fun H => 0 < H.natDegree),
      (C * rawPairUnit dR D H + e)) ≤
        C * (2 * dR * D) + e * dR := by
  classical
  let Hs := (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
    (fun H => 0 < H.natDegree)
  have hdegsum : (∑ H ∈ Hs, H.natDegree) ≤ dR := by
    calc
      (∑ H ∈ Hs, H.natDegree) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset,
            H.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ RX.natDegree := normalizedFactors_toFinset_sum_natDegree_le RX hRX
      _ ≤ dR := hRXdeg
  have htotalsum :
      (∑ H ∈ Hs, Polynomial.Bivariate.totalDegree H) ≤ D := by
    calc
      (∑ H ∈ Hs, Polynomial.Bivariate.totalDegree H) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset,
            Polynomial.Bivariate.totalDegree H := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ Polynomial.Bivariate.totalDegree RX :=
        normalizedFactors_toFinset_sum_totalDegree_le RX hRX
      _ ≤ D := hRXtotal
  have hXsum : (∑ H ∈ Hs, Polynomial.Bivariate.degreeX H) ≤ D := by
    calc
      _ ≤ ∑ H ∈ Hs, Polynomial.Bivariate.totalDegree H := by
        apply Finset.sum_le_sum
        intro H hH
        exact degreeX_le_totalDegree H
      _ ≤ D := htotalsum
  have hcard : Hs.card ≤ dR := by
    calc
      Hs.card = ∑ H ∈ Hs, 1 := by simp
      _ ≤ ∑ H ∈ Hs, H.natDegree := by
        apply Finset.sum_le_sum
        intro H hH
        exact (Finset.mem_filter.mp hH).2
      _ ≤ dR := hdegsum
  have hmain : (∑ H ∈ Hs, C * rawPairUnit dR D H) ≤
      C * (D * dR + dR * D) := by
    calc
      (∑ H ∈ Hs, C * rawPairUnit dR D H) =
          C * (D * (∑ H ∈ Hs, H.natDegree) +
            dR * (∑ H ∈ Hs, Polynomial.Bivariate.degreeX H)) := by
        rw [Finset.mul_sum]
        simp only [rawPairUnit, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
      _ ≤ C * (D * dR + dR * D) := by gcongr
  have heSum : (∑ H ∈ Hs, e) ≤ e * dR := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left e hcard
  calc
    (∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors RX).toFinset.filter
        (fun H => 0 < H.natDegree), (C * rawPairUnit dR D H + e)) =
        (∑ H ∈ Hs, C * rawPairUnit dR D H) + (∑ H ∈ Hs, e) := by
      simp only [Hs, Finset.sum_add_distrib]
    _ ≤ C * (D * dR + dR * D) + e * dR := Nat.add_le_add hmain heSum
    _ = C * (2 * dR * D) + e * dR := by ring

/-- The full 63.95 raw-pair capacity, including all selected-factor bad sets
and the one-time bad-`Z` deletion, has enormous slack. -/
theorem bchks_6395_raw_pair_capacity :
    632281 * (2 * 1001 * 719911) +
      (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 <
        274980000000000000 := by
  norm_num

/-- The exact reduced-gamma resultant degree is strictly below the fiber unit
used by incidence extraction. -/
theorem raw_resultant_cost_lt_pair_unit
    (h d D zdeg : Nat) (hh : 0 < h) (hhd : h ≤ d) (hD : 0 < D) :
    h * (FiniteHenselWeight.denominatorExponent 131071 * D + 1) +
        (FiniteHenselWeight.denominatorExponent 131071 * (d - 1) + 1) * zdeg <
      (2 * 131071 + 2) * (h * D + d * zdeg) := by
  have hd : 0 < d := hh.trans_le hhd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [FiniteHenselWeight.denominatorExponent]
  norm_num
  nlinarith

/-- The pair unit also absorbs deletion of all roots of the specialized
leading coefficient. -/
theorem raw_resultant_plus_leading_bad_lt_pair_unit
    (h d D zdeg : Nat) (hh : 0 < h) (hhd : h ≤ d) (hD : h ≤ D) :
    h * (FiniteHenselWeight.denominatorExponent 131071 * D + 1) +
        (FiniteHenselWeight.denominatorExponent 131071 * (d - 1) + 1) * zdeg +
        (D - h) <
      (2 * 131071 + 2) * (h * D + d * zdeg) := by
  have hd : 0 < d := hh.trans_le hhd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, D = h + q := ⟨D - h, by omega⟩
  simp only [FiniteHenselWeight.denominatorExponent]
  norm_num
  nlinarith

/-- Exact row-to-fiber arithmetic for the 63.99 error cell. -/
theorem incidence_6399_arithmetic (r tcard : Nat)
    (ht : 632746 * r + 76770 + 1 ≤ tcard) :
    (262144 - 76770 - 131071) * tcard >
      (262144 - 131071) * ((2 * 131071 + 2) * r) := by
  norm_num at ht ⊢
  nlinarith

/-- Full 63.99 raw-pair capacity for
`(m,DX,DY,DZ) = (3733,692001142,5280,13141403)`. -/
theorem bchks_6399_raw_pair_capacity :
    632746 * (2 * 5279 * 13141402) +
      (76770 + 1) * 5279 + 2 * 13141403 * 5279 + 13141403 <
        274980000000000000 := by
  norm_num

end SecondStageCapacity
end ProximityPrize.SubmissionLower
