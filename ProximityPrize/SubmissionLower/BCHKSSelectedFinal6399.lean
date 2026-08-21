import ProximityPrize.SubmissionLower.BCHKSStagedUnconditional6399
import ProximityPrize.SubmissionLower.BCHKSSelectedHenselData
import ProximityPrize.SubmissionLower.BCHKSSelectedNonpole
import ProximityPrize.SubmissionLower.BCHKSRawAlignment6395

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem exists_large_domain_fibers_6399
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : T → Polynomial IRSProfile.Field)
    (r : Nat)
    (hrow : ∀ z ∈ T, 262144 - 76770 ≤ (A z).card)
    (hT : 632746 * r + 76770 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + (z : IRSProfile.Field) * U 1 i) :
    ∃ A' : Finset IRSProfile.Field, 131072 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 131071 + 2) * r < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : IRSProfile.Index,
          IRSProfile.domain i = (x : IRSProfile.Field) ∧
          Polynomial.eval (x : IRSProfile.Field) (P z) =
            U 0 i + (z : IRSProfile.Field) * U 1 i := by
  classical
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 131071 + 2) * r < (T.filter fun z => i ∈ A z).card
  have hG : 131072 ≤ G.card := by
    simpa [G] using many_large_fibers T A 262144 76770 131071
      ((2 * 131071 + 2) * r) (by norm_num [IRSProfile.Index]) hrow
      (SecondStageCapacity.incidence_6399_arithmetic r T.card hT)
  let A' : Finset IRSProfile.Field := G.image IRSProfile.domain
  have hA' : A'.card = G.card :=
    Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
  let idx : A' → IRSProfile.Index := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧ IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let Fib : A' → Finset T := fun x => T.attach.filter fun z => idx x ∈ A z
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 131071 + 2) * r <
      (T.attach.filter (fun z : T => idx x ∈ A (z : IRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : IRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : IRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA

theorem selected_pair_final_6399
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → IRSProfile.Field[X])
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    (T : Finset IRSProfile.Field) (x₀ : IRSProfile.Field)
    (Bad : Finset IRSProfile.Field)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0 ∧
      biEval H ((P z).eval x₀) z = 0)
    (hTbad : ∀ z ∈ T, z ∉ Bad)
    (hmargin : 632746 *
      SecondStageCapacity.rawPairUnit R.natDegree 13141402 H +
        (76770 + 1) < T.card)
    (_hRi : Irreducible R) (hRpos : 0 < R.natDegree)
    (hHi : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hHtot : Bivariate.totalDegree H ≤ 13141402)
    (hYZ : YZCap R 13141402)
    (hsimple : ∀ z ∉ Bad, ∀ y,
      Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
      Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0)
    (hrow : ∀ z ∈ T, 262144 - 76770 ≤ (Arow z).card)
    (hagree : ∀ z ∈ T, ∀ i ∈ Arow z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z * U 1 i) :
    ∃ Tgood : Finset IRSProfile.Field, Tgood ⊆ T ∧ 76770 + 1 < Tgood.card ∧
      ∃ p₀ p₁ : IRSProfile.Field[X], p₀.natDegree ≤ 131071 ∧
        p₁.natDegree ≤ 131071 ∧ ∀ z ∈ Tgood,
          P z = p₀ + Polynomial.C z * p₁ := by
  classical
  letI : Fact (Irreducible H) := ⟨hHi⟩
  letI : Fact (0 < H.natDegree) := ⟨hHpos⟩
  let unit := SecondStageCapacity.rawPairUnit R.natDegree 13141402 H
  have hT : 632746 * unit + 76770 + 1 ≤ T.card := by
    simpa [unit, Nat.add_assoc] using hmargin.le
  obtain ⟨A, hA, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers_6399 U T Arow (fun z : T => P z) unit
      hrow hT (fun z i hi => hagree z z.property i hi)
  let Tgood := T.filter fun z => H.leadingCoeff.eval z ≠ 0
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHi.ne_zero
  have hbadW : (T.filter fun z => H.leadingCoeff.eval z = 0).card ≤
      13141402 - H.natDegree := by
    calc
      _ ≤ H.leadingCoeff.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hWne]
        exact (Finset.mem_filter.mp hz).2
      _ ≤ H.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ H.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ 13141402 - H.natDegree :=
        leadingCoeff_natDegree_le_of_totalDegree_le hHtot
  have hpart : Tgood.card + (T.filter fun z => H.leadingCoeff.eval z = 0).card =
      T.card := by
    simpa [Tgood] using Finset.filter_card_add_filter_neg_card_eq_card
      (s := T) (p := fun z => H.leadingCoeff.eval z ≠ 0)
  have hunitD : 13141402 ≤ 632746 * unit := by
    have hu : 13141402 ≤ unit := by
      dsimp [unit, SecondStageCapacity.rawPairUnit]
      have : 1 ≤ H.natDegree := hHpos
      nlinarith
    exact hu.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hTgood_card : 76770 + 1 < Tgood.card := by omega
  let Fibgood : A → Finset Tgood := fun x =>
    let E : {z // z ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0} ↪ Tgood :=
      ⟨fun z => ⟨(z.1 : IRSProfile.Field), Finset.mem_filter.mpr
          ⟨z.1.property, (Finset.mem_filter.mp z.2).2⟩⟩,
        by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun w => ((w : Tgood) : IRSProfile.Field)) hab⟩
    (((Fib x).filter fun z : T =>
      H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).attach).map E
  have hHleR : H.natDegree ≤ R.natDegree :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hHD : H.natDegree ≤ 13141402 := by
    have hHin : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHi.ne_zero)
    have := Bivariate.coeff_totalDegree_le H hHin
    omega
  have hFibgood : ∀ x : A,
      H.natDegree *
          (FiniteHenselWeight.denominatorExponent 131071 * 13141402 + 1) +
        (FiniteHenselWeight.denominatorExponent 131071 * (R.natDegree - 1) + 1) *
          degreeX H < (Fibgood x).card := by
    intro x
    let Fbad := (Fib x).filter fun z : T => H.leadingCoeff.eval (z : IRSProfile.Field) = 0
    have hFbad : Fbad.card ≤ 13141402 - H.natDegree := by
      calc
        Fbad.card = (Fbad.image fun z : T => (z : IRSProfile.Field)).card := by
          symm
          exact Finset.card_image_iff.mpr fun a _ b _ hab => Subtype.ext hab
        _ ≤ (T.filter fun z => H.leadingCoeff.eval z = 0).card := by
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_image] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          exact Finset.mem_filter.mpr ⟨w.property, (Finset.mem_filter.mp hw).2⟩
        _ ≤ _ := hbadW
    have hsplit : ((Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).card + Fbad.card =
        (Fib x).card := by
      simpa [Fbad] using Finset.filter_card_add_filter_neg_card_eq_card
        (s := Fib x) (p := fun z : T => H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0)
    have hrawPlus := SecondStageCapacity.raw_resultant_plus_leading_bad_lt_pair_unit
      H.natDegree R.natDegree 13141402 (degreeX H) hHpos hHleR hHD
    have hlarge := hFib x
    let rawCost := H.natDegree *
        (FiniteHenselWeight.denominatorExponent 131071 * 13141402 + 1) +
      (FiniteHenselWeight.denominatorExponent 131071 * (R.natDegree - 1) + 1) *
        degreeX H
    have hrawPlus' : rawCost + (13141402 - H.natDegree) <
        (2 * 131071 + 2) * unit := by
      simpa [rawCost, unit, SecondStageCapacity.rawPairUnit] using hrawPlus
    have hgood :
        H.natDegree *
            (FiniteHenselWeight.denominatorExponent 131071 * 13141402 + 1) +
          (FiniteHenselWeight.denominatorExponent 131071 * (R.natDegree - 1) + 1) *
            degreeX H <
          ((Fib x).filter fun z : T =>
            H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).card := by
      change rawCost < _
      have hrf : rawCost + Fbad.card < (Fib x).card :=
        (Nat.add_le_add_left hFbad rawCost).trans_lt (hrawPlus'.trans hlarge)
      rw [← hsplit] at hrf
      exact Nat.add_lt_add_iff_right.mp hrf
    dsimp [Fibgood]
    rw [Finset.card_map, Finset.card_attach]
    exact hgood
  have hFibgood_mem (x : A) (z : Tgood) (hz : z ∈ Fibgood x) :
      (⟨(z : IRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ : T) ∈ Fib x := by
    dsimp [Fibgood] at hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : w.1 ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0 := by simpa using hw
    exact (Finset.mem_filter.mp hw').1
  obtain ⟨z₀val, hz₀val⟩ := Finset.card_pos.mp (by omega : 0 < Tgood.card)
  let z₀ : Tgood := ⟨z₀val, hz₀val⟩
  have hz₀T : (z₀ : IRSProfile.Field) ∈ T := (Finset.mem_filter.mp z₀.property).1
  have hz₀W : H.leadingCoeff.eval (z₀ : IRSProfile.Field) ≠ 0 :=
    (Finset.mem_filter.mp z₀.property).2
  let PT : Tgood → IRSProfile.Field[X] := fun z => P z
  have hfactor : ∀ z : Tgood, Polynomial.evalEval (z : IRSProfile.Field)
      ((PT z).eval x₀) H = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C H ((P z).eval x₀) (z : IRSProfile.Field)).symm.trans
      (hvan z (Finset.mem_filter.mp z.property).1).2
  have hExact : ∀ z : Tgood,
      (triSpecializeZ R (z : IRSProfile.Field)).eval (PT z) = 0 := by
    intro z
    simpa [PT, triEval_eq_eval_triSpecializeZ] using
      (hvan z (Finset.mem_filter.mp z.property).1).1
  let root : ∀ z : Tgood, rationalRoot (monicize H) (z : IRSProfile.Field) := fun z =>
    rationalRootOfPair H hHpos (z : IRSProfile.Field) ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : Tgood, GoodAt (z : IRSProfile.Field) (root z)
      (fieldTo𝕃 (H := H) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H := H) (z : IRSProfile.Field) (root z) x₀
  have hslope_eval (z x y : IRSProfile.Field) :
      FiniteHensel.ySlope (triSpecializeZ R z) x y =
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x) z) := by
    simp only [FiniteHensel.ySlope, triSpecializeZ, triSpecializeX, biSpecializeZ,
      Polynomial.derivative_map]
    induction Polynomial.derivative R using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a => simp [eval_map_eval_eq_eval_eval_C]
  have hsimp : ∀ z : Tgood, FiniteHensel.ySlope
      (triSpecializeZ R (z : IRSProfile.Field)) x₀ ((PT z).eval x₀) ≠ 0 := by
    intro z
    rw [hslope_eval]
    apply hsimple z (hTbad z (Finset.mem_filter.mp z.property).1) ((P z).eval x₀)
    exact (eval_triEval_eq_biEval_triSpecializeX R (P z) x₀
      (z : IRSProfile.Field)).symm.trans
        (by
          have hz := congrArg
            (fun q : Polynomial IRSProfile.Field => Polynomial.eval x₀ q)
            (hvan z (Finset.mem_filter.mp z.property).1).1
          simpa using hz)
  let root₀ := root z₀
  have hx₀ := hx z₀
  have hy₀ : GoodAt (z₀ : IRSProfile.Field) root₀ (initialValue (H := H))
      ((PT z₀).eval x₀) := by
    have hT : GoodAt (z₀ : IRSProfile.Field) root₀ (functionFieldT (H := H))
        (H.leadingCoeff.eval (z₀ : IRSProfile.Field) * (PT z₀).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1,
        ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root, root₀] using
          (piZ_mk_X_rationalRootOfPair H hHpos (z₀ : IRSProfile.Field)
            ((PT z₀).eval x₀) (hfactor z₀)).symm
    have hWgood := GoodAt.liftToFunctionField (H := H)
      (z₀ : IRSProfile.Field) root₀ H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ hz₀W] using GoodAt.div hT hWgood hz₀W
  have hs₀ : FiniteHensel.ySlope (triSpecializeZ R (z₀ : IRSProfile.Field)) x₀
      ((PT z₀).eval x₀) ≠ 0 := hsimp z₀
  have hzeta := zeta_ne_zero_of_selected_slope x₀ R (z₀ : IRSProfile.Field) root₀ x₀
    ((PT z₀).eval x₀) hx₀ hy₀ hs₀
  have hy : ∀ z : Tgood, GoodAt (z : IRSProfile.Field) (root z)
      (initialValue (H := H)) ((PT z).eval x₀) := by
    intro z
    have hT : GoodAt (z : IRSProfile.Field) (root z) (functionFieldT (H := H))
        (H.leadingCoeff.eval (z : IRSProfile.Field) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1,
        ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using (piZ_mk_X_rationalRootOfPair H hHpos
          (z : IRSProfile.Field) ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H := H)
      (z : IRSProfile.Field) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _
      (Finset.mem_filter.mp z.property).2] using
        GoodAt.div hT hWgood (Finset.mem_filter.mp z.property).2
  have hNP : ∀ z : Tgood, SelectedNonpoleData x₀ R H hHyp (z : IRSProfile.Field)
      (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ R hHyp hzeta (z : IRSProfile.Field) (root z) x₀
      ((PT z).eval x₀) (hx z) (hy z)
      (Finset.mem_filter.mp z.property).2 (hsimp z)
  have hPdegT : ∀ z : Tgood, (PT z).natDegree ≤ 131071 := fun z =>
    hPdeg z (Finset.mem_filter.mp z.property).1
  have hsimpleT : ∀ z : Tgood, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z : IRSProfile.Field)) x₀ ((PT z).eval x₀) := by
    intro z
    refine ⟨?_, hsimp z⟩
    have hz := congrArg (fun q : IRSProfile.Field[X] => q.eval x₀) (hExact z)
    calc
      _ = (Polynomial.evalRingHom x₀)
          (Polynomial.eval (PT z) (triSpecializeZ R (z : IRSProfile.Field))) := by
        change Polynomial.eval₂ ((Polynomial.evalRingHom x₀).comp (RingHom.id IRSProfile.Field[X]))
            ((Polynomial.evalRingHom x₀) (PT z)) (triSpecializeZ R (z : IRSProfile.Field)) =
          (Polynomial.evalRingHom x₀)
            (Polynomial.eval₂ (RingHom.id IRSProfile.Field[X]) (PT z)
              (triSpecializeZ R (z : IRSProfile.Field)))
        exact (Polynomial.hom_eval₂ (triSpecializeZ R (z : IRSProfile.Field))
          (RingHom.id IRSProfile.Field[X]) (Polynomial.evalRingHom x₀) (PT z)).symm
      _ = 0 := by simpa using hz
  have hne : ∀ x : A, (Fib x).Nonempty := fun x =>
    Finset.card_pos.mp (Nat.zero_lt_of_lt (hFib x))
  let zpick : ∀ x : A, T := fun x => Classical.choose (hne x)
  have hzpick (x : A) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : A → IRSProfile.Index := fun x =>
    Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : A) : IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 0 (idx ⟨x, hx⟩) else 0
  let U₁ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : A, ∀ z ∈ Fibgood x,
      (PT z).eval (x : IRSProfile.Field) = U₀ x + (z : IRSProfile.Field) * U₁ x := by
    intro x z hz
    have hzFib := hFibgood_mem x z hz
    obtain ⟨i, hi, he⟩ := hinc x
      ⟨(z : IRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ hzFib
    have hii : i = idx x := IRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [PT, U₀, U₁, x.property] using he
  obtain ⟨p₀, p₁, hp₀, hp₁, hp⟩ := hensel_baseZ_alignment_final_raw
    x₀ R hHyp hzeta 13141402 131071 131072 (by norm_num) hYZ hRpos
    Tgood root PT hPdegT hfactor hx hy
    (hNP z₀).hsL hsimpleT hExact
    (fun z => (hNP z).hslope) (fun z => (Finset.mem_filter.mp z.property).2)
    (fun z => (hNP z).hxi)
    (fun t _ z => (hNP z).hden t) (by norm_num [IRSProfile.Field])
    A (by simpa using hA) U₀ U₁ Fibgood hFibgood halign rfl
  exact ⟨Tgood, Finset.filter_subset _ _, hTgood_card, p₀, p₁, hp₀, hp₁,
    fun z hz => hp ⟨z, hz⟩⟩

end ProximityPrize.SubmissionLower
