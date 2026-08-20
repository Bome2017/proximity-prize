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
abbrev extra := 8391
abbrev agreement := 139463
abbrev signatureWidth := 8391
abbrev unsafeIndex := 122681

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, Benchmark.IRSProfile.interleaving]⟩

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

theorem base_field_pow_8403_lt_two_pow_260493 :
    (Fintype.card K) ^ 8403 < 2 ^ 260493 := by
  have hpow : ∀ q : Nat, q < 2 ^ 31 → q ^ 8403 < 2 ^ 260493 := by
    intro q hq
    calc
      q ^ 8403 < (2 ^ 31) ^ 8403 :=
        Nat.pow_lt_pow_left hq (by norm_num)
      _ = 2 ^ (31 * 8403) := (pow_mul 2 31 8403).symm
      _ = 2 ^ 260493 := by norm_num
  exact hpow (Fintype.card K) base_field_card_lt_two_pow_31

theorem signature_sieve_lt_two_pow_260493 :
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 <
      2 ^ 260493 := by
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
      q ^ signatureWidth * q ^ 12 = q ^ 8403 := by
    intro q
    change q ^ 8391 * q ^ 12 = q ^ 8403
    rw [← pow_add]
  calc
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 ≤
        (Fintype.card K) ^ signatureWidth * (Fintype.card K) ^ 12 := by
      rw [hsig, hcardF, hcardK]
      exact hmul _root_.KoalaBear.fieldSize signatureWidth
    _ = (Fintype.card K) ^ 8403 := hcombine (Fintype.card K)
    _ < 2 ^ 260493 := base_field_pow_8403_lt_two_pow_260493

set_option maxRecDepth 1000000

theorem seven_mul_choose_le_two_mul_choose_add_two {n j : Nat}
    (hjn : j ≤ n)
    (hratio : 7 * (n + 1 - j) * (n + 2 - j) ≤
      2 * ((n + 1) * (n + 2))) :
    7 * Nat.choose n j ≤ 2 * Nat.choose (n + 2) j := by
  have hd1 : 0 < n + 1 - j := by omega
  have hd2 : 0 < n + 2 - j := by omega
  have heq : Nat.choose n j * (n + 1) * (n + 2) =
      Nat.choose (n + 2) j * (n + 1 - j) * (n + 2 - j) := by
    calc
      Nat.choose n j * (n + 1) * (n + 2) =
          (Nat.choose (n + 1) j * (n + 1 - j)) * (n + 2) := by
            rw [Nat.choose_mul_succ_eq]
      _ = (Nat.choose (n + 1) j * (n + 2)) * (n + 1 - j) := by ring
      _ = (Nat.choose (n + 2) j * (n + 2 - j)) * (n + 1 - j) := by
            rw [Nat.choose_mul_succ_eq]
      _ = Nat.choose (n + 2) j * (n + 1 - j) * (n + 2 - j) := by ring
  apply Nat.le_of_mul_le_mul_right (c := (n + 1 - j) * (n + 2 - j))
  · calc
      (7 * Nat.choose n j) * ((n + 1 - j) * (n + 2 - j)) =
          Nat.choose n j * (7 * (n + 1 - j) * (n + 2 - j)) := by ring
      _ ≤ Nat.choose n j * (2 * ((n + 1) * (n + 2))) :=
        Nat.mul_le_mul_left _ hratio
      _ = 2 * (Nat.choose n j * (n + 1) * (n + 2)) := by ring
      _ = 2 * (Nat.choose (n + 2) j * (n + 1 - j) * (n + 2 - j)) := by
        rw [heq]
      _ = (2 * Nat.choose (n + 2) j) *
          ((n + 1 - j) * (n + 2 - j)) := by ring
  · exact Nat.mul_pos hd1 hd2

theorem seven_pow_mul_central_le_two_pow_mul_choose_steps
    (j d : Nat)
    (hj : 2 ≤ j)
    (hratio : ∀ i < d,
      7 * (2 * j + 2 * i + 1 - j) * (2 * j + 2 * i + 2 - j) ≤
        2 * ((2 * j + 2 * i + 1) * (2 * j + 2 * i + 2))) :
    7 ^ d * Nat.centralBinom j ≤
      2 ^ d * Nat.choose (2 * j + 2 * d) j := by
  induction d with
  | zero =>
      simp [Nat.centralBinom_eq_two_mul_choose]
  | succ d ih =>
      have ih' := ih (fun i hi => hratio i (Nat.lt_succ_of_lt hi))
      have hstep := seven_mul_choose_le_two_mul_choose_add_two
        (n := 2 * j + 2 * d) (j := j) (by omega) (hratio d (by omega))
      calc
        7 ^ (d + 1) * Nat.centralBinom j =
            7 * (7 ^ d * Nat.centralBinom j) := by rw [pow_succ]; ring
        _ ≤ 7 * (2 ^ d * Nat.choose (2 * j + 2 * d) j) :=
          Nat.mul_le_mul_left 7 ih'
        _ = 2 ^ d * (7 * Nat.choose (2 * j + 2 * d) j) := by ring
        _ ≤ 2 ^ d * (2 * Nat.choose (2 * j + 2 * d + 2) j) :=
          Nat.mul_le_mul_left _ hstep
        _ = 2 ^ (d + 1) * Nat.choose (2 * j + 2 * (d + 1)) j := by
          rw [pow_succ,
            show 2 * j + 2 * d + 2 = 2 * j + 2 * (d + 1) by omega]
          ac_rfl

theorem ratio_122681_8391 : ∀ i < 8391,
    7 * (2 * 122681 + 2 * i + 1 - 122681) *
          (2 * 122681 + 2 * i + 2 - 122681) ≤
      2 * ((2 * 122681 + 2 * i + 1) *
        (2 * 122681 + 2 * i + 2)) := by
  intro i hi
  have hsub1 : 2 * 122681 + 2 * i + 1 - 122681 = 122682 + 2 * i := by
    omega
  have hsub2 : 2 * 122681 + 2 * i + 2 - 122681 = 122683 + 2 * i := by
    omega
  rw [hsub1, hsub2]
  have h1 : 15 * (122682 + 2 * i) ≤
      8 * (2 * 122681 + 2 * i + 1) := by omega
  have h2 : 15 * (122683 + 2 * i) ≤
      8 * (2 * 122681 + 2 * i + 2) := by omega
  apply Nat.le_of_mul_le_mul_left (c := 32) (by
    calc
      32 * (7 * (122682 + 2 * i) * (122683 + 2 * i)) =
          224 * ((122682 + 2 * i) * (122683 + 2 * i)) := by ring
      _ ≤ 225 * ((122682 + 2 * i) * (122683 + 2 * i)) := by
        exact Nat.mul_le_mul_right _ (by norm_num)
      _ = (15 * (122682 + 2 * i)) * (15 * (122683 + 2 * i)) := by ring
      _ ≤ (8 * (2 * 122681 + 2 * i + 1)) *
          (8 * (2 * 122681 + 2 * i + 2)) :=
        mul_le_mul h1 h2 (by omega) (by omega)
      _ = 32 * (2 * ((2 * 122681 + 2 * i + 1) *
          (2 * 122681 + 2 * i + 2))) := by ring) (by norm_num)

theorem seven_pow_8391_mul_central_le :
    7 ^ 8391 * Nat.centralBinom 122681 ≤
      2 ^ 8391 * Nat.choose 262144 122681 := by
  have h := seven_pow_mul_central_le_two_pow_mul_choose_steps
    122681 8391 (by norm_num) ratio_122681_8391
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

theorem two_pow_245345_lt_central_122681 :
    2 ^ 245345 < Nat.centralBinom 122681 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 122681 (by norm_num)
  by_contra hnot
  have hle : Nat.centralBinom 122681 ≤ 2 ^ 245345 := Nat.le_of_not_gt hnot
  have hbad : 4 ^ 122681 < 122681 * 2 ^ 245345 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 122681 hle)
  have hreverse : 122681 * 2 ^ 245345 < 4 ^ 122681 := by
    calc
      122681 * 2 ^ 245345 < 2 ^ 17 * 2 ^ 245345 := by
        gcongr <;> norm_num
      _ = 2 ^ (17 + 245345) := (pow_add 2 17 245345).symm
      _ = 2 ^ (2 * 122681) := by norm_num
      _ = (2 ^ 2) ^ 122681 := pow_mul 2 2 122681
      _ = 4 ^ 122681 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem two_pow_23556_lt_seven_pow_8391 : 2 ^ 23556 < 7 ^ 8391 := by
  have hbase : 2 ^ 306 < 7 ^ 109 := by
    calc
      2 ^ 306 = (2 ^ 153) ^ 2 := by
        convert pow_mul 2 153 2 using 1 <;> norm_num
      _ < 7 ^ 109 := by norm_num
  have hbulk : (2 ^ 306) ^ 76 < (7 ^ 109) ^ 76 :=
    Nat.pow_lt_pow_left hbase (by norm_num)
  have htail : 2 ^ 300 < 7 ^ 107 := by
    calc
      2 ^ 300 = (2 ^ 150) ^ 2 := by
        convert pow_mul 2 150 2 using 1 <;> norm_num
      _ < 7 ^ 107 := by norm_num
  have hproduct : (2 ^ 306) ^ 76 * 2 ^ 300 <
      (7 ^ 109) ^ 76 * 7 ^ 107 :=
    mul_lt_mul hbulk htail.le (by positivity) (by positivity)
  calc
    2 ^ 23556 = (2 ^ 306) ^ 76 * 2 ^ 300 := by
      rw [← pow_mul, ← pow_add]
    _ < (7 ^ 109) ^ 76 * 7 ^ 107 := hproduct
    _ = 7 ^ 8391 := by
      rw [← pow_mul, ← pow_add]

theorem two_pow_260493_lt_candidate_choose :
    2 ^ 260493 < Nat.choose 262144 139463 := by
  have hproduct :
      2 ^ 23556 * 2 ^ 245345 <
        7 ^ 8391 * Nat.centralBinom 122681 :=
    mul_lt_mul two_pow_23556_lt_seven_pow_8391
      two_pow_245345_lt_central_122681.le (by positivity) (by positivity)
  have hscaled :
      2 ^ 8391 * 2 ^ 260510 <
        2 ^ 8391 * Nat.choose 262144 122681 := by
    calc
      2 ^ 8391 * 2 ^ 260510 = 2 ^ 268901 := by rw [← pow_add]
      _ = 2 ^ 23556 * 2 ^ 245345 := by rw [← pow_add]
      _ < 7 ^ 8391 * Nat.centralBinom 122681 := hproduct
      _ ≤ 2 ^ 8391 * Nat.choose 262144 122681 :=
        seven_pow_8391_mul_central_le
  have hstrong : 2 ^ 260510 < Nat.choose 262144 122681 :=
    Nat.lt_of_mul_lt_mul_left hscaled
  calc
    2 ^ 260493 < 2 ^ 260510 :=
      Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ < Nat.choose 262144 122681 := hstrong
    _ = Nat.choose 262144 139463 := Nat.choose_symm_of_eq_add (by norm_num)

theorem two_pow_260493_lt_card_candidateSets :
    2 ^ 260493 < Fintype.card CandidateSets := by
  have hconcrete : 2 ^ 260493 < Nat.choose 262144 139463 :=
    two_pow_260493_lt_candidate_choose
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  have hcardI : Nat.card I = 262144 := by
    rw [I, Benchmark.IRSProfile.Index, Nat.card_fin]
    norm_num
  rw [hcardI]
  exact hconcrete

theorem signature_card_mul_field_sq_lt :
    Fintype.card (Fin signatureWidth → K) * (Fintype.card F - 1) ^ 2 <
      Fintype.card CandidateSets :=
  signature_sieve_lt_two_pow_260493.trans
    two_pow_260493_lt_card_candidateSets

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
  by_cases htop : n = agreement
  · subst n
    have ha := (rootPolyK_monic anchor.1).coeff_natDegree
    have hT := (rootPolyK_monic T.1).coeff_natDegree
    rw [rootPolyK_natDegree] at ha hT
    rw [ha, hT, sub_self]
  · by_cases hna : n ≤ agreement
    · have hi : n - rowK < signatureWidth := by
        norm_num [agreement, rowK, signatureWidth] at hna hn htop ⊢
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
