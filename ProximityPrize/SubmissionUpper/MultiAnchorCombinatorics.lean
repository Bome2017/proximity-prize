/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetUpper

namespace ProximityPrize.SubmissionUpper.MultiAnchor

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped BigOperators NNReal

set_option maxRecDepth 100000

abbrev K := _root_.KoalaBear.Field
abbrev F := _root_.KoalaBear.Ext6
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev rowK := 131072
abbrev quotientSize := 512
abbrev fiberSize := 512
abbrev locatorSize := 272
abbrev anchorCount := 14
abbrev familySize := 2 ^ 58
abbrev agreement := 139775
abbrev unsafeIndex := 122369
abbrev bridgeIndex := 122642

namespace IRSProfile

open ProximityPrize.Benchmark

/-- The canonical embedding of the KoalaBear base field into its sextic extension. -/
def emb : K →+* F :=
  CompPoly.Extension.Ext.ofBaseRingHom _root_.KoalaBear.ext6Params

theorem emb_injective : Function.Injective emb := RingHom.injective emb

abbrev D := Benchmark.IRSProfile.baseNttDomain

abbrev omega : K := D.omega

/-- A primitive 512-th root obtained by quotienting the size-2^18 NTT domain. -/
abbrev zeta : K := omega ^ fiberSize

theorem zeta_primitive : IsPrimitiveRoot zeta quotientSize := by
  have hdiv : fiberSize ∣ 2 ^ D.logN := by
    change 512 ∣ 2 ^ 18
    norm_num
  have h := D.primitive.pow_of_dvd (p := fiberSize)
    (by norm_num [fiberSize]) hdiv
  have horder : 2 ^ D.logN / fiberSize = quotientSize := by
    change 2 ^ 18 / 512 = 512
    norm_num
  change IsPrimitiveRoot (D.omega ^ fiberSize) quotientSize
  rw [← horder]
  exact h

/-- The 511 nontrivial quotient roots from which locators are chosen. -/
def locatorNode (i : Fin 511) : K := zeta ^ (i.1 + 1)

theorem locatorNode_injective : Function.Injective locatorNode := by
  intro i j hij
  apply Fin.ext
  apply Nat.add_right_cancel
  exact zeta_primitive.pow_inj
    (by
      have hi := i.isLt
      change i.1 + 1 < 512
      omega)
    (by
      have hj := j.isLt
      change j.1 + 1 < 512
      omega)
    hij

/-- Fourteen explicit base-field anchors outside the quotient subgroup. -/
def anchorNode (i : Fin anchorCount) : K := omega ^ (i.1 + 1)

theorem anchorNode_injective : Function.Injective anchorNode := by
  intro i j hij
  apply Fin.ext
  apply Nat.add_right_cancel
  exact D.primitive.pow_inj
    (by
      have hi := i.isLt
      change i.1 + 1 < 2 ^ 18
      change i.1 < 14 at hi
      omega)
    (by
      have hj := j.isLt
      change j.1 + 1 < 2 ^ 18
      change j.1 < 14 at hj
      omega)
    hij

theorem anchorNode_ne_zero (i : Fin anchorCount) : anchorNode i ≠ 0 := by
  exact pow_ne_zero _ (D.primitive.ne_zero (by
    norm_num [D, Benchmark.IRSProfile.baseNttDomain]))

theorem anchorNode_ne_quotient (i : Fin anchorCount) (r : Fin quotientSize) :
    anchorNode i ≠ zeta ^ r.1 := by
  intro h
  have heq : omega ^ (i.1 + 1) = omega ^ (fiberSize * r.1) := by
    simpa [anchorNode, zeta, pow_mul] using h
  have hiLt : i.1 < anchorCount := i.isLt
  have hrLt : r.1 < quotientSize := r.isLt
  change i.1 < 14 at hiLt
  change r.1 < 512 at hrLt
  have hexp : i.1 + 1 = fiberSize * r.1 :=
    D.primitive.pow_inj
      (by
        change i.1 + 1 < 2 ^ 18
        omega)
      (by
        change 512 * r.1 < 2 ^ 18
        omega)
      heq
  have hi : 0 < i.1 + 1 := by omega
  have hsmall : i.1 + 1 < fiberSize := by
    change i.1 + 1 < 512
    omega
  rcases Nat.eq_zero_or_pos r.1 with hr | hr
  · simp [hr] at hexp
  · have : fiberSize ≤ fiberSize * r.1 := Nat.le_mul_of_pos_right _ hr
    omega

abbrev CandidateSets := Set.powersetCard (Fin 511) locatorSize

noncomputable instance : Fintype CandidateSets := Fintype.ofFinite _

noncomputable def rootPolyK (T : CandidateSets) : Polynomial K :=
  (T.1 : Finset (Fin 511)).prod fun i =>
    Polynomial.X - Polynomial.C (locatorNode i)

theorem rootPolyK_monic (T : CandidateSets) : (rootPolyK T).Monic := by
  simpa only [rootPolyK] using
    (Polynomial.monic_prod_X_sub_C (fun i : Fin 511 => locatorNode i) (T.1 : Finset _))

theorem rootPolyK_natDegree (T : CandidateSets) :
    (rootPolyK T).natDegree = locatorSize := by
  rw [rootPolyK, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  exact T.prop

noncomputable def exponentSignature (T : CandidateSets) : Fin quotientSize :=
  ⟨(∑ i ∈ (T.1 : Finset (Fin 511)), (i.1 + 1)) % quotientSize,
    Nat.mod_lt _ (by norm_num [quotientSize])⟩

noncomputable def signature (T : CandidateSets) :
    Fin quotientSize × (Fin anchorCount → K) :=
  (exponentSignature T, fun i => (rootPolyK T).eval (anchorNode i))

private theorem locator_prod_eq_zeta_sum (T : CandidateSets) :
    ∏ i ∈ (T.1 : Finset (Fin 511)), locatorNode i =
      zeta ^ (∑ i ∈ (T.1 : Finset (Fin 511)), (i.1 + 1)) := by
  simp only [locatorNode]
  rw [Finset.prod_pow_eq_pow_sum]

theorem rootPolyK_eval_zero_eq_of_exponentSignature_eq (A B : CandidateSets)
    (h : exponentSignature A = exponentSignature B) :
    (rootPolyK A).eval 0 = (rootPolyK B).eval 0 := by
  have hmod :
      (∑ i ∈ (A.1 : Finset (Fin 511)), (i.1 + 1)) ≡
        (∑ i ∈ (B.1 : Finset (Fin 511)), (i.1 + 1)) [MOD quotientSize] := by
    change
      (∑ i ∈ (A.1 : Finset (Fin 511)), (i.1 + 1)) % quotientSize =
        (∑ i ∈ (B.1 : Finset (Fin 511)), (i.1 + 1)) % quotientSize
    exact congrArg Fin.val h
  have hpow := pow_eq_pow_of_modEq hmod zeta_primitive.pow_eq_one
  rw [rootPolyK, rootPolyK, Polynomial.eval_prod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rw [show (∏ i ∈ (A.1 : Finset (Fin 511)), -locatorNode i) =
      (-1 : K) ^ locatorSize *
        ∏ i ∈ (A.1 : Finset (Fin 511)), locatorNode i by
      rw [Finset.prod_neg, A.prop],
    show (∏ i ∈ (B.1 : Finset (Fin 511)), -locatorNode i) =
      (-1 : K) ^ locatorSize *
        ∏ i ∈ (B.1 : Finset (Fin 511)), locatorNode i by
      rw [Finset.prod_neg, B.prop],
    locator_prod_eq_zeta_sum, locator_prod_eq_zeta_sum, hpow]

theorem rootPolyK_eval_anchor_eq_of_signature_eq (A B : CandidateSets)
    (h : signature A = signature B) (i : Fin anchorCount) :
    (rootPolyK A).eval (anchorNode i) = (rootPolyK B).eval (anchorNode i) := by
  exact congrFun (congrArg Prod.snd h) i

theorem signature_card_mul_family_lt_candidate_card :
    Fintype.card (Fin quotientSize × (Fin anchorCount → K)) * familySize <
      Fintype.card CandidateSets := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    show Fintype.card K = _root_.KoalaBear.fieldSize by exact ZMod.card _]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp only [Nat.card_fin]
  rw [Nat.choose_eq_fast_choose]
  norm_num [quotientSize, anchorCount, familySize, locatorSize,
    _root_.KoalaBear.fieldSize, Nat.fast_choose, Nat.descFactorial]

lemma exists_large_fiber {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (sieve : Nat)
    (hlarge : Fintype.card β * sieve < Fintype.card α) :
    ∃ y : β, sieve < (Finset.univ.filter fun x : α => f x = y).card := by
  classical
  by_contra! hall
  have hsum : Fintype.card α =
      ∑ y : β, (Finset.univ.filter fun x : α => f x = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (f := f)
      (fun _ _ => Finset.mem_univ _))
  have hle : Fintype.card α ≤ Fintype.card β * sieve := by
    rw [hsum]
    calc
      (∑ y : β, (Finset.univ.filter fun x : α => f x = y).card) ≤
          ∑ _y : β, sieve := Finset.sum_le_sum fun y _ => hall y
      _ = Fintype.card β * sieve := by simp
  omega

theorem exists_signature_fiber :
    ∃ y : Fin quotientSize × (Fin anchorCount → K),
      familySize < (Finset.univ.filter fun T : CandidateSets => signature T = y).card :=
  exists_large_fiber signature familySize signature_card_mul_family_lt_candidate_card

noncomputable def chosenSignature : Fin quotientSize × (Fin anchorCount → K) :=
  Classical.choose exists_signature_fiber

noncomputable def fullFiber : Finset CandidateSets :=
  Finset.univ.filter fun T => signature T = chosenSignature

theorem familySize_le_fullFiber_card : familySize ≤ fullFiber.card := by
  exact (Classical.choose_spec exists_signature_fiber).le

theorem exists_chosenSets :
    ∃ S : Finset CandidateSets, S ⊆ fullFiber ∧ S.card = familySize :=
  Finset.exists_subset_card_eq familySize_le_fullFiber_card

noncomputable def chosenSets : Finset CandidateSets := Classical.choose exists_chosenSets

theorem chosenSets_subset_fullFiber : chosenSets ⊆ fullFiber :=
  (Classical.choose_spec exists_chosenSets).1

theorem chosenSets_card : chosenSets.card = familySize :=
  (Classical.choose_spec exists_chosenSets).2

abbrev ChosenSets := ↥chosenSets

theorem chosen_member_signature (T : ChosenSets) : signature T.1 = chosenSignature := by
  exact (Finset.mem_filter.mp (chosenSets_subset_fullFiber T.2)).2

theorem chosen_exponentSignature_eq (A B : ChosenSets) :
    exponentSignature A.1 = exponentSignature B.1 := by
  exact congrArg Prod.fst ((chosen_member_signature A).trans (chosen_member_signature B).symm)

theorem chosen_eval_zero_eq (A B : ChosenSets) :
    (rootPolyK A.1).eval 0 = (rootPolyK B.1).eval 0 :=
  rootPolyK_eval_zero_eq_of_exponentSignature_eq A.1 B.1 (chosen_exponentSignature_eq A B)

theorem chosen_eval_anchor_eq (A B : ChosenSets) (i : Fin anchorCount) :
    (rootPolyK A.1).eval (anchorNode i) =
      (rootPolyK B.1).eval (anchorNode i) :=
  rootPolyK_eval_anchor_eq_of_signature_eq A.1 B.1
    ((chosen_member_signature A).trans (chosen_member_signature B).symm) i

noncomputable def rootPoly (T : CandidateSets) : Polynomial F :=
  (rootPolyK T).map emb

theorem rootPoly_monic (T : CandidateSets) : (rootPoly T).Monic :=
  (rootPolyK_monic T).map emb

theorem rootPoly_natDegree (T : CandidateSets) : (rootPoly T).natDegree = locatorSize := by
  rw [rootPoly, Polynomial.natDegree_map_eq_of_injective emb_injective,
    rootPolyK_natDegree]

theorem rootPoly_injective : Function.Injective rootPoly := by
  intro A B hAB
  apply Subtype.ext
  by_contra hne
  have hABne : A ≠ B := fun h => hne (congrArg Subtype.val h)
  obtain ⟨i, hiA, hiB⟩ :=
    (Set.powersetCard.exists_mem_notMem_iff_ne A B).mp hABne
  have hzeroA : (rootPoly A).eval (emb (locatorNode i)) = 0 := by
    have hbase : (rootPolyK A).eval (locatorNode i) = 0 := by
      rw [rootPolyK, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (i := i)
      · exact hiA
      · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    simpa [rootPoly] using congrArg emb hbase
  have hneB : (rootPoly B).eval (emb (locatorNode i)) ≠ 0 := by
    have hbase : (rootPolyK B).eval (locatorNode i) ≠ 0 := by
      rw [rootPolyK, Polynomial.eval_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      exact fun heq => hiB (by
        have hij := locatorNode_injective heq
        subst j
        exact hj)
    intro hzero
    exact hbase (emb_injective (by simpa [rootPoly] using hzero))
  exact hneB (hAB ▸ hzeroA)

theorem rootPoly_sub_natDegree_le (A B : CandidateSets) :
    (rootPoly A - rootPoly B).natDegree ≤ 271 := by
  by_cases hAB : A = B
  · subst B
    simp
  · have hdeg : (rootPoly A - rootPoly B).degree < (locatorSize : Nat) := by
      calc
        (rootPoly A - rootPoly B).degree < (rootPoly A).degree :=
          Polynomial.degree_sub_lt (by
            rw [Polynomial.degree_eq_natDegree (rootPoly_monic A).ne_zero,
              Polynomial.degree_eq_natDegree (rootPoly_monic B).ne_zero,
              rootPoly_natDegree, rootPoly_natDegree])
            (rootPoly_monic A).ne_zero (by
              rw [(rootPoly_monic A).leadingCoeff, (rootPoly_monic B).leadingCoeff])
        _ = (locatorSize : Nat) := by
          rw [Polynomial.degree_eq_natDegree (rootPoly_monic A).ne_zero,
            rootPoly_natDegree]
    have hne : rootPoly A - rootPoly B ≠ 0 := sub_ne_zero.mpr (rootPoly_injective.ne hAB)
    have hnatlt := (Polynomial.natDegree_lt_iff_degree_lt hne).2 hdeg
    norm_num [locatorSize] at hnatlt ⊢
    omega

noncomputable def quotientNodesF : Finset F :=
  Finset.univ.image fun r : Fin quotientSize => emb (zeta ^ r.1)

theorem quotientNodesF_card : quotientNodesF.card = quotientSize := by
  rw [quotientNodesF, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact zeta_primitive.pow_inj i.isLt j.isLt (emb_injective hij)

noncomputable def anchorNodesF : Finset F :=
  Finset.univ.image fun i : Fin anchorCount => emb (anchorNode i)

theorem anchorNodesF_card : anchorNodesF.card = anchorCount := by
  rw [anchorNodesF, Finset.card_image_of_injective]
  · simp
  · exact emb_injective.comp anchorNode_injective

noncomputable def fixedPoints : Finset F := insert 0 anchorNodesF

theorem zero_not_mem_anchorNodesF : 0 ∉ anchorNodesF := by
  simp only [anchorNodesF, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro i h
  exact anchorNode_ne_zero i (emb_injective (by simpa using h))

theorem fixedPoints_card : fixedPoints.card = 15 := by
  rw [fixedPoints, Finset.card_insert_of_notMem zero_not_mem_anchorNodesF, anchorNodesF_card]

noncomputable def W0 : Polynomial F :=
  fixedPoints.prod fun a => Polynomial.X - Polynomial.C a

theorem W0_monic : W0.Monic := by
  simpa only [W0] using Polynomial.monic_prod_X_sub_C (fun a : F => a) fixedPoints

theorem W0_natDegree : W0.natDegree = 15 := by
  rw [W0, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, fixedPoints_card]

noncomputable def collisionRoots : Finset F :=
  chosenSets.offDiag.biUnion fun AB => (rootPoly AB.1 - rootPoly AB.2).roots.toFinset

noncomputable def forbidden : Finset F :=
  collisionRoots ∪ W0.roots.toFinset ∪ quotientNodesF

theorem collisionRoots_card_le :
    collisionRoots.card ≤ familySize * (familySize - 1) * 271 := by
  classical
  calc
    collisionRoots.card ≤ ∑ AB ∈ chosenSets.offDiag,
        (rootPoly AB.1 - rootPoly AB.2).roots.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _AB ∈ chosenSets.offDiag, 271 := by
      apply Finset.sum_le_sum
      intro AB hAB
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (rootPoly_sub_natDegree_le _ _))
    _ = familySize * (familySize - 1) * 271 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, chosenSets_card]
      simp only [Nat.mul_sub_left_distrib, mul_one]
      ac_rfl

theorem forbidden_card_lt_field : forbidden.card < Fintype.card F := by
  have hW : W0.roots.toFinset.card ≤ 15 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans_eq W0_natDegree)
  have hq := quotientNodesF_card
  have hc := collisionRoots_card_le
  have hcardF : Fintype.card F = _root_.KoalaBear.fieldSize ^ 6 :=
    _root_.KoalaBear.card_ext6
  calc
    forbidden.card ≤ collisionRoots.card + W0.roots.toFinset.card + quotientNodesF.card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ familySize * (familySize - 1) * 271 + 15 + quotientSize := by omega
    _ < Fintype.card F := by
      rw [hcardF]
      norm_num [familySize, quotientSize, _root_.KoalaBear.fieldSize]

theorem exists_lambda : ∃ x : F, x ∉ forbidden := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := forbidden) (t := (Finset.univ : Finset F)) (by simpa using forbidden_card_lt_field)
  exact ⟨x, hx⟩

noncomputable def lambda : F := Classical.choose exists_lambda

theorem lambda_not_mem_forbidden : lambda ∉ forbidden := Classical.choose_spec exists_lambda

theorem lambda_not_mem_quotientNodesF : lambda ∉ quotientNodesF := by
  exact fun h => lambda_not_mem_forbidden (by simp [forbidden, h])

theorem W0_eval_lambda_ne_zero : W0.eval lambda ≠ 0 := by
  intro h
  have hroot : lambda ∈ W0.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots W0_monic.ne_zero]
    simpa [Polynomial.IsRoot.def] using h
  exact lambda_not_mem_forbidden (by simp [forbidden, hroot])

theorem eval_lambda_injective :
    Function.Injective (fun T : ChosenSets => (rootPoly T.1).eval lambda) := by
  intro A B hAB
  by_contra hne
  have hval : A.1 ≠ B.1 := fun h => hne (Subtype.ext h)
  have hoff : (A.1, B.1) ∈ chosenSets.offDiag := by
    exact Finset.mem_offDiag.mpr ⟨A.2, B.2, hval⟩
  have hroot : lambda ∈ (rootPoly A.1 - rootPoly B.1).roots.toFinset := by
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (sub_ne_zero.mpr (rootPoly_injective.ne hval))]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, hAB, sub_self]
  have hcoll : lambda ∈ collisionRoots := by
    rw [collisionRoots, Finset.mem_biUnion]
    exact ⟨(A.1, B.1), hoff, by simpa using hroot⟩
  exact lambda_not_mem_forbidden (by simp [forbidden, hcoll])

end IRSProfile
end ProximityPrize.SubmissionUpper.MultiAnchor
