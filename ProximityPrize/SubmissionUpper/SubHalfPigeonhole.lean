/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped BigOperators NNReal

abbrev K := _root_.KoalaBear.Field
abbrev F := _root_.KoalaBear.Ext6
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving
abbrev rowK := 131072
abbrev extra := 8100
abbrev agreement := 139172
abbrev signatureWidth := 8101
abbrev unsafeIndex := 122972

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, Benchmark.IRSProfile.interleaving]⟩

set_option maxHeartbeats 400000

theorem rowDimension_eq : k / s = rowK :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [rowK, Benchmark.IRSProfile.baseDimension])

abbrev CandidateSets := Set.powersetCard I agreement

noncomputable instance : Fintype CandidateSets := Fintype.ofFinite _

def emb : K →+* F :=
  CompPoly.Extension.Ext.ofBaseRingHom _root_.KoalaBear.ext6Params

theorem emb_injective : Function.Injective emb := RingHom.injective emb

def baseDomain : I ↪ K where
  toFun i := Benchmark.IRSProfile.baseNttDomain.node i
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Benchmark.IRSProfile.baseNttDomain.primitive.pow_inj i.isLt j.isLt hij

@[simp] theorem emb_baseDomain (i : I) :
    emb (baseDomain i) = Benchmark.IRSProfile.domain i := rfl

noncomputable def baseNodes (T : CandidateSets) : Finset K :=
  (T : Finset I).image baseDomain

theorem card_baseNodes (T : CandidateSets) : (baseNodes T).card = agreement := by
  rw [baseNodes, Finset.card_image_of_injective _ baseDomain.injective]
  exact T.prop

noncomputable def rootPolyK (T : CandidateSets) : Polynomial K :=
  (baseNodes T).prod fun a => Polynomial.X - Polynomial.C a

theorem rootPolyK_monic (T : CandidateSets) : (rootPolyK T).Monic := by
  simpa only [rootPolyK] using
    (Polynomial.monic_prod_X_sub_C (fun x : K => x) (baseNodes T))

theorem rootPolyK_natDegree (T : CandidateSets) :
    (rootPolyK T).natDegree = agreement := by
  rw [rootPolyK, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_baseNodes]

noncomputable def signature (T : CandidateSets) : Fin signatureWidth → K :=
  fun i => (rootPolyK T).coeff (rowK + i)

noncomputable def rootPoly (T : CandidateSets) : Polynomial F :=
  (rootPolyK T).map emb

theorem rootPoly_monic (T : CandidateSets) : (rootPoly T).Monic := by
  exact (rootPolyK_monic T).map emb

theorem rootPoly_natDegree (T : CandidateSets) :
    (rootPoly T).natDegree = agreement := by
  rw [rootPoly, Polynomial.natDegree_map_eq_of_injective emb_injective,
    rootPolyK_natDegree]

theorem base_field_card_lt_two_pow_31 : Fintype.card K < 2 ^ 31 := by
  rw [ZMod.card]
  norm_num [_root_.KoalaBear.fieldSize]

lemma mul_pred_cross {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * (n - k) ≤ n * (n + 1 - k) := by
  rw [Nat.succ_sub hk, Nat.succ_mul, Nat.mul_succ]
  exact Nat.add_le_add_left (Nat.sub_le n k) _

lemma choose_ge_scaled_central (k t : ℕ) :
    Nat.choose (2 * k) k * (2 * k + t) ^ t ≤
      Nat.choose (2 * k + t) k * (k + t) ^ t := by
  have hk2 : k ≤ 2 * k := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
  induction t with
  | zero => simp
  | succ t ih =>
    set n := 2 * k + t
    have hn : 2 * k ≤ n := Nat.le_add_right _ _
    have hkn : k ≤ n := hk2.trans hn
    have hnk : n - k = k + t := by
      change 2 * k + t - k = k + t
      rw [Nat.two_mul, Nat.add_assoc, Nat.add_sub_cancel_left]
    have hnpos : 0 < n ^ t := by
      cases t with
      | zero => simp
      | succ _ => exact Nat.pow_pos (by omega)
    rw [show 2 * k + t.succ = n + 1 from rfl, pow_succ, pow_succ]
    have hkt : k + t.succ = n + 1 - k := by
      have hsucc : n + 1 - k = n - k + 1 := Nat.succ_sub hkn
      rw [hsucc, hnk, Nat.succ_eq_add_one, Nat.add_assoc]
    rw [hkt]
    have hmul := Nat.choose_mul_succ_eq n k
    have hcross := mul_pred_cross hkn
    have hcrossPow :
        (n + 1) ^ t * (n - k) ^ t ≤ n ^ t * (n + 1 - k) ^ t := by
      simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hcross t
    have hreduced :
        Nat.choose (2 * k) k * (n + 1) ^ t ≤
          Nat.choose n k * (n + 1 - k) ^ t := by
      have hih :
          Nat.choose (2 * k) k * n ^ t ≤
            Nat.choose n k * (n - k) ^ t := by
        simpa only [hnk] using ih
      have hmulIH :
          Nat.choose (2 * k) k * n ^ t * (n + 1) ^ t ≤
            Nat.choose n k * (n - k) ^ t * (n + 1) ^ t :=
        Nat.mul_le_mul_right _ hih
      have hchain :
          Nat.choose n k * (n - k) ^ t * (n + 1) ^ t ≤
            Nat.choose n k * n ^ t * (n + 1 - k) ^ t := by
        simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          Nat.mul_le_mul_left (Nat.choose n k) hcrossPow
      have := hmulIH.trans hchain
      exact Nat.le_of_mul_le_mul_left (by
        simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this) hnpos
    have hfinal :
        Nat.choose (2 * k) k * ((n + 1) ^ t * (n + 1)) ≤
          Nat.choose (n + 1) k * ((n + 1 - k) ^ t * (n + 1 - k)) := by
      have h1 :
          Nat.choose (2 * k) k * ((n + 1) ^ t * (n + 1)) =
            Nat.choose (2 * k) k * (n + 1) ^ t * (n + 1) :=
        (Nat.mul_assoc _ _ _).symm
      have h2 := Nat.mul_le_mul_right (n + 1) hreduced
      have h3 :
          Nat.choose n k * (n + 1 - k) ^ t * (n + 1) =
            (n + 1 - k) ^ t * (Nat.choose n k * (n + 1)) := by
        rw [Nat.mul_assoc, Nat.mul_left_comm (Nat.choose n k)]
      have h4 :
          (n + 1 - k) ^ t * (Nat.choose n k * (n + 1)) =
            (n + 1 - k) ^ t * (Nat.choose (n + 1) k * (n + 1 - k)) := by
        rw [hmul]
      have h5 :
          (n + 1 - k) ^ t * (Nat.choose (n + 1) k * (n + 1 - k)) =
            Nat.choose (n + 1) k * ((n + 1 - k) ^ t * (n + 1 - k)) :=
        Nat.mul_left_comm ((n + 1 - k) ^ t) (Nat.choose (n + 1) k) (n + 1 - k)
      rw [h1]
      exact h2.trans_eq (h3.trans (h4.trans h5))
    exact hfinal

theorem base_field_pow_8113_lt_two_pow_251503 :
    (Fintype.card K) ^ 8113 < 2 ^ 251503 := by
  have hpow : ∀ q : Nat, q < 2 ^ 31 → q ^ 8113 < 2 ^ 251503 := by
    intro q hq
    calc
      q ^ 8113 < (2 ^ 31) ^ 8113 :=
        Nat.pow_lt_pow_left hq (by norm_num)
      _ = 2 ^ (31 * 8113) := (pow_mul 2 31 8113).symm
      _ = 2 ^ 251503 := by norm_num
  exact hpow (Fintype.card K) base_field_card_lt_two_pow_31

theorem signature_sieve_lt_two_pow_251503 :
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 <
      2 ^ 251503 := by
  have hcardF : Fintype.card F = _root_.KoalaBear.fieldSize ^ 6 := by
    exact _root_.KoalaBear.card_ext6
  have hcardK : Fintype.card K = _root_.KoalaBear.fieldSize := by
    exact ZMod.card _
  have hfun : ∀ w : Nat, Fintype.card (Fin w → K) =
      (Fintype.card K) ^ w := fun w => by
    simpa only [Fintype.card_fin] using
      (Fintype.card_fun : Fintype.card (Fin w → K) =
        Fintype.card K ^ Fintype.card (Fin w))
  have hsig : Fintype.card (Fin signatureWidth → K) =
      (Fintype.card K) ^ signatureWidth := hfun signatureWidth
  have hmul : ∀ q w : Nat,
      q ^ w * (q ^ 6 - 1) ^ 2 ≤ q ^ w * q ^ 12 := by
    intro q w
    apply Nat.mul_le_mul_left
    calc
      (q ^ 6 - 1) ^ 2 ≤ (q ^ 6) ^ 2 :=
        Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      _ = q ^ 12 := by rw [← pow_mul]
  have hcombine : ∀ q : Nat,
      q ^ signatureWidth * q ^ 12 = q ^ 8113 := by
    intro q
    change q ^ 8101 * q ^ 12 = q ^ 8113
    rw [← pow_add]
  calc
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 ≤
        (Fintype.card K) ^ signatureWidth * (Fintype.card K) ^ 12 := by
      rw [hsig, hcardF, hcardK]
      exact hmul _root_.KoalaBear.fieldSize signatureWidth
    _ = (Fintype.card K) ^ 8113 := hcombine (Fintype.card K)
    _ < 2 ^ 251503 := base_field_pow_8113_lt_two_pow_251503

theorem agr_sq_lt_two_pow_35 : 139172 ^ 2 < 2 ^ 35 := by
  norm_num

lemma pow_two_mul (a n : ℕ) : a ^ (2 * n) = (a ^ 2) ^ n :=
  pow_mul a 2 n

theorem agr_pow_16200_lt_two_pow_283500 :
    139172 ^ 16200 < 2 ^ 283500 := by
  have hgen : ∀ a : ℕ, a ^ 2 < 2 ^ 35 → a ^ (2 * 8100) < 2 ^ (35 * 8100) := by
    intro a h
    rw [pow_two_mul, pow_mul]
    exact Nat.pow_lt_pow_left h (by norm_num)
  exact hgen 139172 agr_sq_lt_two_pow_35

theorem two_pow_251503_lt_choose :
    2 ^ 251503 < Nat.choose 262144 122972 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 122972 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  have hscale : Nat.choose 245944 122972 * 262144 ^ 16200 ≤
      Nat.choose 262144 122972 * 139172 ^ 16200 := by
    have h := choose_ge_scaled_central 122972 16200
    norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
    exact h
  have hfour :
      4 ^ 122972 * 262144 ^ 16200 <
        122972 * Nat.choose 262144 122972 * 139172 ^ 16200 := by
    have hmid :
        4 ^ 122972 * 262144 ^ 16200 <
          (122972 * Nat.choose 245944 122972) * 262144 ^ 16200 :=
      Nat.mul_lt_mul_of_pos_right hcentral
        (Nat.pow_pos (by norm_num : 0 < 262144))
    have hstep :
        4 ^ 122972 * 262144 ^ 16200 <
          122972 * (Nat.choose 262144 122972 * 139172 ^ 16200) :=
      (hmid.trans_eq (Nat.mul_assoc _ _ _)).trans_le
        (Nat.mul_le_mul_left _ hscale)
    exact hstep.trans_eq (Nat.mul_assoc _ _ _).symm
  have hright :
      122972 * 139172 ^ 16200 * 2 ^ 251503 <
        4 ^ 122972 * 262144 ^ 16200 := by
    have hi : 122972 < 2 ^ 17 := by norm_num
    have hagr : 139172 ^ 16200 < 2 ^ 283500 :=
      agr_pow_16200_lt_two_pow_283500
    have hprod : 122972 * 139172 ^ 16200 < 2 ^ (17 + 283500) := by
      rw [pow_add]
      have h1 : 122972 * 139172 ^ 16200 < 2 ^ 17 * 139172 ^ 16200 :=
        Nat.mul_lt_mul_of_pos_right hi
          (Nat.pow_pos (by norm_num : 0 < 139172))
      have h2 : 2 ^ 17 * 139172 ^ 16200 < 2 ^ 17 * 2 ^ 283500 :=
        Nat.mul_lt_mul_of_pos_left hagr (Nat.pow_pos (by norm_num : 0 < 2))
      exact h1.trans h2
    have h4 : 4 = 2 ^ 2 := by norm_num
    have hn : 262144 = 2 ^ 18 := by norm_num
    rw [h4, hn]
    rw [← pow_mul, ← pow_mul]
    rw [← pow_add]
    refine Nat.lt_trans ?_
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by
        norm_num : (17 + 283500) + 251503 < 2 * 122972 + 18 * 16200))
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hprod
      (Nat.pow_pos (by norm_num : 0 < 2))
  by_contra hnot
  have hle : Nat.choose 262144 122972 ≤ 2 ^ 251503 :=
    Nat.le_of_not_gt hnot
  have hbad :
      4 ^ 122972 * 262144 ^ 16200 <
        122972 * 139172 ^ 16200 * 2 ^ 251503 := by
    have hrearr :
        122972 * Nat.choose 262144 122972 * 139172 ^ 16200 =
          122972 * 139172 ^ 16200 * Nat.choose 262144 122972 :=
      Nat.mul_right_comm _ _ _
    have hmul :=
      Nat.mul_le_mul_left (122972 * 139172 ^ 16200) hle
    exact (hfour.trans_eq hrearr).trans_le hmul
  exact (Nat.not_lt_of_ge hright.le) hbad

theorem two_pow_251503_lt_card_candidateSets :
    2 ^ 251503 < Fintype.card CandidateSets := by
  have hconcrete : 2 ^ 251503 < Nat.choose 262144 139172 := by
    calc
      2 ^ 251503 < Nat.choose 262144 122972 := two_pow_251503_lt_choose
      _ = Nat.choose 262144 139172 := Nat.choose_symm_of_eq_add (by omega)
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  have hcardI : Nat.card I = 262144 := by
    rw [I, Benchmark.IRSProfile.Index, Nat.card_fin]
    norm_num
  rw [hcardI]
  exact hconcrete

theorem signature_card_mul_field_sq_lt :
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 <
      Fintype.card CandidateSets :=
  signature_sieve_lt_two_pow_251503.trans
    two_pow_251503_lt_card_candidateSets

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
          ∑ _y : β, sieve := by
        exact Finset.sum_le_sum fun y _ => hall y
      _ = Fintype.card β * sieve := by simp
  omega

theorem exists_signature_fiber :
    ∃ y : Fin signatureWidth → K,
      (Fintype.card F - 1) ^ 2 <
        (Finset.univ.filter fun T : CandidateSets => signature T = y).card := by
  exact exists_large_fiber signature ((Fintype.card F - 1) ^ 2)
    signature_card_mul_field_sq_lt

noncomputable def chosenSignature : Fin signatureWidth → K :=
  Classical.choose exists_signature_fiber

noncomputable def fiberSets : Finset CandidateSets :=
  Finset.univ.filter fun T => signature T = chosenSignature

abbrev FiberSets := ↥fiberSets

theorem card_fiberSets_large :
    (Fintype.card F - 1) ^ 2 < Fintype.card FiberSets := by
  rw [Fintype.card_coe]
  exact Classical.choose_spec exists_signature_fiber

theorem fiberSets_nonempty : fiberSets.Nonempty := by
  apply Finset.card_pos.mp
  rw [← Fintype.card_coe]
  exact lt_of_le_of_lt (Nat.zero_le _) card_fiberSets_large

noncomputable def anchor : FiberSets :=
  ⟨Classical.choose fiberSets_nonempty, Classical.choose_spec fiberSets_nonempty⟩

theorem member_signature (T : FiberSets) :
    signature T.1 = chosenSignature := by
  exact (Finset.mem_filter.mp T.2).2

noncomputable def diffPolyK (T : FiberSets) : Polynomial K :=
  rootPolyK anchor.1 - rootPolyK T.1

theorem diffPolyK_degree_lt (T : FiberSets) :
    (diffPolyK T).degree < (rowK : Nat) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [diffPolyK, Polynomial.coeff_sub]
  by_cases hna : n ≤ agreement
  · have hi : n - rowK < signatureWidth := by
      norm_num [agreement, rowK, signatureWidth] at hna hn ⊢
      omega
    let i : Fin signatureWidth := ⟨n - rowK, hi⟩
    have hs := congrFun
      ((member_signature anchor).trans (member_signature T).symm) i
    have hadd : rowK + (n - rowK) = n := Nat.add_sub_of_le hn
    rw [signature, signature, show rowK + i.1 = n by simpa [i] using hadd] at hs
    exact sub_eq_zero.mpr hs
  · have hgt : agreement < n := Nat.lt_of_not_ge hna
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (rootPolyK_natDegree anchor.1 ▸ hgt),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (rootPolyK_natDegree T.1 ▸ hgt), sub_zero]

noncomputable def diffPoly (T : FiberSets) : Polynomial F :=
  (diffPolyK T).map emb

theorem diffPoly_degree_lt (T : FiberSets) :
    (diffPoly T).degree < (rowK : Nat) := by
  rw [diffPoly, Polynomial.degree_map_eq_of_injective emb_injective]
  exact diffPolyK_degree_lt T

theorem diffPoly_eq (T : FiberSets) :
    diffPoly T = rootPoly anchor.1 - rootPoly T.1 := by
  simp only [diffPoly, diffPolyK, rootPoly, Polynomial.map_sub]

noncomputable def coeff (T : FiberSets) : Fin (k / s) → F :=
  Polynomial.degreeLTEquiv F (k / s) ⟨diffPoly T, by
    rw [Polynomial.mem_degreeLT]
    simpa only [rowDimension_eq] using diffPoly_degree_lt T⟩

noncomputable def rows (T : FiberSets) : Fin s → Fin (k / s) → F :=
  fun row => if row = 0 then coeff T else 0

noncomputable def message (T : FiberSets) : Fin k → F :=
  flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension (rows T)

theorem rsPolynomial_coeff (T : FiberSets) :
    ToyProblem.Spec.rsPolynomial (k / s) (coeff T) = diffPoly T := by
  exact congrArg Subtype.val
    ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply
      ⟨diffPoly T, by
        rw [Polynomial.mem_degreeLT]
        simpa only [rowDimension_eq] using diffPoly_degree_lt T⟩)

noncomputable def fixedWord : I → Fin s → F :=
  fun j row => if row = 0 then (rootPoly anchor.1).eval
    (Benchmark.IRSProfile.domain j) else 0

theorem rootPoly_eval_eq_zero (T : CandidateSets) (j : I)
    (hj : j ∈ (T : Finset I)) :
    (rootPoly T).eval (Benchmark.IRSProfile.domain j) = 0 := by
  have hbase : (rootPolyK T).eval (baseDomain j) = 0 := by
    classical
    rw [rootPolyK, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := baseDomain j)
    · simp [baseNodes, hj]
    · simp
  rw [← emb_baseDomain, rootPoly, Polynomial.eval_map,
    Polynomial.eval₂_hom, hbase, map_zero]

theorem fixedWord_agrees (T : FiberSets) :
    ∀ j ∈ (T.1 : Finset I),
      fixedWord j = Benchmark.IRSProfile.encoder (message T) j := by
  intro j hj
  funext row
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change fixedWord j row = ToyProblem.Spec.rsEncoder (k / s)
    Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
        (flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
          (rows T)) row) j
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows T 0 = coeff T by simp [rows],
      ToyProblem.Spec.rsEncoder_apply, rsPolynomial_coeff]
    simp only [fixedWord, if_pos, diffPoly_eq, Polynomial.eval_sub]
    rw [rootPoly_eval_eq_zero T.1 j hj, sub_zero]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [fixedWord, rows, hrow] using hz.symm

theorem no_message_agrees_on_more_than_agreement
    (u : Fin k → F) (S : Finset I) (hcard : agreement < S.card)
    (hagree : ∀ j ∈ S, fixedWord j = Benchmark.IRSProfile.encoder u j) : False := by
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (rowK : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hrootdeg : (rootPoly anchor.1).degree < (S.card : Nat) := by
    rw [Polynomial.degree_eq_natDegree (rootPoly_monic anchor.1).ne_zero,
      rootPoly_natDegree]
    exact_mod_cast hcard
  have hqdegS : q.degree < (S.card : Nat) := by
    have hrS : rowK < S.card :=
      (show rowK < agreement by norm_num [rowK, agreement]).trans hcard
    exact hqdeg.trans (by exact_mod_cast hrS)
  have heval : ∀ j ∈ S,
      (rootPoly anchor.1).eval (Benchmark.IRSProfile.domain j) =
        q.eval (Benchmark.IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin s)
    rw [Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at h
    simpa [fixedWord, q] using h
  have heq : rootPoly anchor.1 = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      S Benchmark.IRSProfile.domain.injective.injOn hrootdeg hqdegS heval
  have hqnat : q.natDegree < rowK := by
    by_cases hqzero : q = 0
    · simp [hqzero, rowK]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have hnat := congrArg Polynomial.natDegree heq
  rw [rootPoly_natDegree] at hnat
  norm_num [agreement, rowK] at hnat hqnat
  omega

theorem message_eq_zero_of_zero_on_many (u : Fin k → F) (S : Finset I)
    (hcard : rowK ≤ S.card)
    (hzero : ∀ j ∈ S, Benchmark.IRSProfile.encoder u j = 0) : u = 0 := by
  have hu := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := u) (by simpa only [rowDimension_eq] using hcard) hzero
  have hz := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := (0 : Fin k → F))
    (by simpa only [rowDimension_eq] using hcard) (by
      intro j hj
      exact congrFun (map_zero Benchmark.IRSProfile.encoder) j)
  rw [← hu, hz]

theorem message_injective : Function.Injective message := by
  intro A B hAB
  by_contra hne
  have hval : A.1 ≠ B.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hcardUnion : agreement <
      ((A.1 : Finset I) ∪ (B.1 : Finset I)).card := by
    obtain ⟨i, hiA, hiB⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne A.1 B.1).mp hval
    have hBsub : (B.1 : Finset I) ⊆
        (A.1 : Finset I) ∪ (B.1 : Finset I) := Finset.subset_union_right
    have hBstrict : (B.1 : Finset I) ⊂
        (A.1 : Finset I) ∪ (B.1 : Finset I) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, ?_⟩
      intro heq
      have hiUnion : i ∈ (A.1 : Finset I) ∪ (B.1 : Finset I) :=
        Finset.mem_union_left _ hiA
      have : i ∈ (B.1 : Finset I) := by rwa [← heq] at hiUnion
      exact hiB this
    have hlt := Finset.card_lt_card hBstrict
    simpa only [Set.powersetCard.card_eq B.1] using hlt
  apply no_message_agrees_on_more_than_agreement
    (message A) ((A.1 : Finset I) ∪ (B.1 : Finset I)) hcardUnion
  intro j hj
  rcases Finset.mem_union.mp hj with hjA | hjB
  · exact fixedWord_agrees A j hjA
  · rw [hAB]
    exact fixedWord_agrees B j hjB

theorem winningSetSoundness_eq_one
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico
      (ProximityGap.gridPt (ι := I) unsafeIndex)
      Benchmark.IRSProfile.minRelativeDistance) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  apply HalfRadiusCollision.winningSetSoundness_eq_one_of_large_fixed_word_list
    (F := F) Benchmark.IRSProfile.encoder δ
    (m := agreement) (z := rowK) (J := FiberSets)
    (p := message) (T := fun T => (T.1 : Finset I)) (f := fixedWord)
  · have hlt : (δ : ℝ) < 131073 / 262144 := by
      exact_mod_cast hδ.2
    norm_num [rowK, I, Benchmark.IRSProfile.Index,
      Benchmark.IRSProfile.minRelativeDistance] at hlt ⊢
    linarith
  · have hgeGrid :
        ((ProximityGap.gridPt (ι := I) unsafeIndex : ℝ≥0) : ℝ) ≤ (δ : ℝ) :=
      NNReal.coe_le_coe.mpr hδ.1
    have hge : (unsafeIndex : ℝ) / 262144 ≤ δ := by
      norm_num [ProximityGap.gridPt, unsafeIndex, I,
        Benchmark.IRSProfile.Index] at hgeGrid ⊢
      exact hgeGrid
    norm_num [agreement, unsafeIndex, I, Benchmark.IRSProfile.Index] at hge ⊢
    linarith
  · exact message_injective
  · exact card_fiberSets_large
  · intro T
    exact T.1.prop
  · exact fixedWord_agrees
  · exact message_eq_zero_of_zero_on_many

end IRSProfile
end ProximityPrize.SubmissionUpper.SubHalfPigeonhole
