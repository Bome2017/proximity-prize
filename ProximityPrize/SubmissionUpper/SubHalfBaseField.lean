/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Base-field pigeonhole with a SHARP central-binomial bound. The root polynomial's
top coefficients live in the prime field `KoalaBear.Field` (elementary symmetric
functions of base-field node values), so the pigeonhole is over `p^signatureWidth`
buckets. The binomial lower bound uses a 15/8 growth ratio
`choose(2N, N-d) ≥ (15/8)^{2d}·centralBinom(N-d)`, sharper than the 3/2 ratio,
pushing the certified unsafe radius to 122687/2^18 (B = 11655). The growth
constant is certified through the tight ladder `15^10 ≥ 2^39`.
-/
import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.SubHalfBaseField

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped BigOperators NNReal

set_option maxRecDepth 500000

abbrev F := ProximityPrize.Benchmark.IRSProfile.Field
abbrev BF := _root_.KoalaBear.Field
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving
abbrev rowK := 131072
abbrev extra := 8385
abbrev agreement := 139457
abbrev signatureWidth := 8386
abbrev unsafeIndex := 122687

/-- The prime-field → sextic ring hom; `φ c = Ext.ofBase c` definitionally. -/
noncomputable def φ : BF →+* F :=
  CompPoly.Extension.Ext.ofBaseRingHom _root_.KoalaBear.ext6Params

theorem φ_injective : Function.Injective φ := φ.injective

/-- The base-field node underlying each domain point. -/
noncomputable def baseNode (j : I) : BF :=
  ProximityPrize.Benchmark.IRSProfile.baseNttDomain.node j

theorem domain_eq (j : I) :
    ProximityPrize.Benchmark.IRSProfile.domain j = φ (baseNode j) := rfl

theorem baseNode_injective : Function.Injective baseNode := by
  intro a b hab
  apply ProximityPrize.Benchmark.IRSProfile.domain.injective
  rw [domain_eq, domain_eq, hab]

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = rowK :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [rowK, Benchmark.IRSProfile.baseDimension])

abbrev CandidateSets := Set.powersetCard I agreement

noncomputable instance : Fintype CandidateSets := Fintype.ofFinite _

theorem card_candidateSets :
    Fintype.card CandidateSets = Nat.choose 262144 agreement := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  norm_num [I, agreement, Benchmark.IRSProfile.Index]

/-! ## Root polynomial over the extension, and its base-field preimage -/

noncomputable def nodes (T : CandidateSets) : Finset F :=
  (T : Finset I).image Benchmark.IRSProfile.domain

theorem card_nodes (T : CandidateSets) : (nodes T).card = agreement := by
  rw [nodes, Finset.card_image_of_injective _ Benchmark.IRSProfile.domain.injective]
  exact T.prop

noncomputable def rootPoly (T : CandidateSets) : Polynomial F :=
  (nodes T).prod fun a => Polynomial.X - Polynomial.C a

theorem rootPoly_monic (T : CandidateSets) : (rootPoly T).Monic := by
  simpa only [rootPoly] using
    (Polynomial.monic_prod_X_sub_C (fun x : F => x) (nodes T))

theorem rootPoly_natDegree (T : CandidateSets) :
    (rootPoly T).natDegree = agreement := by
  rw [rootPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_nodes]

noncomputable def baseNodes (T : CandidateSets) : Finset BF :=
  (T : Finset I).image _root_.ProximityPrize.SubmissionUpper.SubHalfBaseField.baseNode

noncomputable def baseRootPoly (T : CandidateSets) : Polynomial BF :=
  (baseNodes T).prod fun b => Polynomial.X - Polynomial.C b

/-- The extension root polynomial is the base-field one pushed through `φ`. -/
theorem rootPoly_eq_map (T : CandidateSets) :
    rootPoly T = (baseRootPoly T).map φ := by
  rw [baseRootPoly, Polynomial.map_prod]
  rw [rootPoly, nodes, baseNodes,
    Finset.prod_image (fun a _ b _ h =>
      _root_.ProximityPrize.SubmissionUpper.SubHalfBaseField.baseNode_injective h),
    Finset.prod_image (fun a _ b _ h =>
      Benchmark.IRSProfile.domain.injective h)]
  apply Finset.prod_congr rfl
  intro j _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    _root_.ProximityPrize.SubmissionUpper.SubHalfBaseField.domain_eq]

/-! ## Signatures: base-field valued, bridged to the extension signature -/

noncomputable def signature (T : CandidateSets) : Fin signatureWidth → F :=
  fun i => (rootPoly T).coeff (rowK + i)

noncomputable def baseSig (T : CandidateSets) : Fin signatureWidth → BF :=
  fun i => (baseRootPoly T).coeff (rowK + i)

theorem signature_eq_map (T : CandidateSets) (i : Fin signatureWidth) :
    signature T i = φ (baseSig T i) := by
  rw [signature, baseSig, rootPoly_eq_map, Polynomial.coeff_map]

/-! ## The base-field pigeonhole with a sharp 15/8 growth bound -/

theorem field_card_lt_two_pow_186 : Fintype.card F < 2 ^ 186 := by
  change Fintype.card _root_.KoalaBear.Ext6 < 2 ^ 186
  rw [_root_.KoalaBear.card_ext6]
  norm_num [_root_.KoalaBear.fieldSize]

theorem base_field_card_lt_two_pow_31 : Fintype.card BF < 2 ^ 31 := by
  rw [_root_.ZMod.card]
  norm_num [_root_.KoalaBear.fieldSize]

theorem base_field_pow_lt : (Fintype.card BF) ^ 8398 < 2 ^ 260338 := by
  have hpow : ∀ q : Nat, q < 2 ^ 31 → q ^ 8398 < 2 ^ 260338 := by
    intro q hq
    calc
      q ^ 8398 < (2 ^ 31) ^ 8398 := Nat.pow_lt_pow_left hq (by norm_num)
      _ = 2 ^ (31 * 8398) := (pow_mul 2 31 8398).symm
      _ = 2 ^ 260338 := by norm_num
  exact hpow (Fintype.card BF) base_field_card_lt_two_pow_31

theorem signature_sieve_lt :
    Fintype.card (Fin signatureWidth → BF) * (Fintype.card F - 1) ^ 2 <
      2 ^ 260338 := by
  have hcardF : Fintype.card F = _root_.KoalaBear.fieldSize ^ 6 :=
    _root_.KoalaBear.card_ext6
  have hcardK : Fintype.card BF = _root_.KoalaBear.fieldSize := _root_.ZMod.card _
  have hfun : ∀ w : Nat, Fintype.card (Fin w → BF) = (Fintype.card BF) ^ w :=
    fun w => by
      simpa only [Fintype.card_fin] using
        (Fintype.card_fun : Fintype.card (Fin w → BF) =
          Fintype.card BF ^ Fintype.card (Fin w))
  have hsig : Fintype.card (Fin signatureWidth → BF) =
      (Fintype.card BF) ^ signatureWidth := hfun signatureWidth
  have hmul : ∀ q w : Nat, q ^ w * (q ^ 6 - 1) ^ 2 ≤ q ^ w * q ^ 12 := by
    intro q w
    apply Nat.mul_le_mul_left
    calc
      (q ^ 6 - 1) ^ 2 ≤ (q ^ 6) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      _ = q ^ 12 := by rw [← pow_mul]
  have hcombine : ∀ q : Nat, q ^ signatureWidth * q ^ 12 = q ^ 8398 := by
    intro q
    change q ^ 8386 * q ^ 12 = q ^ 8398
    rw [← pow_add]
  calc
    Fintype.card (Fin signatureWidth → BF) * (Fintype.card F - 1) ^ 2 ≤
        (Fintype.card BF) ^ signatureWidth * (Fintype.card BF) ^ 12 := by
      rw [hsig, hcardF, hcardK]
      exact hmul _root_.KoalaBear.fieldSize signatureWidth
    _ = (Fintype.card BF) ^ 8398 := hcombine (Fintype.card BF)
    _ < 2 ^ 260338 := base_field_pow_lt

/-- One 15/8 growth step: `15·choose n j ≤ 8·choose (n+1) j` when `7(n+1) ≤ 15 j`. -/
theorem fifteen_mul_choose_le_eight_mul_choose_succ {n j : Nat}
    (hpos : 0 < n + 1 - j) (hratio : 7 * (n + 1) ≤ 15 * j) :
    15 * Nat.choose n j ≤ 8 * Nat.choose (n + 1) j := by
  refine Nat.le_of_mul_le_mul_right (c := n + 1 - j) ?_ hpos
  calc
    (15 * Nat.choose n j) * (n + 1 - j) =
        Nat.choose n j * (15 * (n + 1 - j)) := by ac_rfl
    _ ≤ Nat.choose n j * (8 * (n + 1)) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 8 * (Nat.choose n j * (n + 1)) := by ac_rfl
    _ = 8 * (Nat.choose (n + 1) j * (n + 1 - j)) := by rw [Nat.choose_mul_succ_eq]
    _ = (8 * Nat.choose (n + 1) j) * (n + 1 - j) := by ac_rfl

theorem fifteen_pow_mul_choose_le_eight_pow_mul_choose_add {n j t : Nat}
    (hj : j ≤ n) (hsteps : 7 * (n + t) ≤ 15 * j) :
    15 ^ t * Nat.choose n j ≤ 8 ^ t * Nat.choose (n + t) j := by
  induction t with
  | zero => simp
  | succ t ih =>
      specialize ih (by omega)
      have hjn : j ≤ n + t := hj.trans (Nat.le_add_right n t)
      have hpos : 0 < n + t + 1 - j := by omega
      have hstep := fifteen_mul_choose_le_eight_mul_choose_succ hpos (by omega)
      calc
        15 ^ (t + 1) * Nat.choose n j = 15 * (15 ^ t * Nat.choose n j) := by
          rw [pow_succ]; ac_rfl
        _ ≤ 15 * (8 ^ t * Nat.choose (n + t) j) := Nat.mul_le_mul_left 15 ih
        _ = 8 ^ t * (15 * Nat.choose (n + t) j) := by ac_rfl
        _ ≤ 8 ^ t * (8 * Nat.choose (n + t + 1) j) :=
          Nat.mul_le_mul_left (8 ^ t) hstep
        _ = 8 ^ (t + 1) * Nat.choose (n + (t + 1)) j := by
          rw [pow_succ, show n + t + 1 = n + (t + 1) by omega]; ac_rfl

/-- One 31/16 growth step. -/
theorem two_pow_lt_central_choose :
    2 ^ 245357 < Nat.choose 245374 122687 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 122687 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hle : Nat.choose 245374 122687 ≤ 2 ^ 245357 := Nat.le_of_not_gt hnot
  have hbad : 4 ^ 122687 < 122687 * 2 ^ 245357 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 122687 hle)
  have hreverse : 122687 * 2 ^ 245357 < 4 ^ 122687 := by
    calc
      122687 * 2 ^ 245357 < 2 ^ 17 * 2 ^ 245357 := by gcongr <;> norm_num
      _ = 2 ^ (17 + 245357) := (pow_add 2 17 245357).symm
      _ = (2 ^ 2) ^ 122687 := by convert pow_mul 2 2 122687 using 1 <;> norm_num
      _ = 4 ^ 122687 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem two_pow_lt_choose : 2 ^ 260338 < Nat.choose 262144 122687 := by
  have hgrowth :
      15 ^ 16770 * Nat.choose 245374 122687 ≤
        8 ^ 16770 * Nat.choose 262144 122687 := by
    have h := fifteen_pow_mul_choose_le_eight_pow_mul_choose_add
      (n := 245374) (j := 122687) (t := 16770) (by norm_num) (by norm_num)
    norm_num only [Nat.reduceAdd] at h
    exact h
  have h15 : (2 : ℕ) ^ 65403 ≤ 15 ^ 16770 := by
    calc
      (2 : ℕ) ^ 65403 = (2 ^ 39) ^ 1677 := by
        rw [show (65403 : ℕ) = 39 * 1677 from by norm_num, pow_mul]
      _ ≤ (15 ^ 10) ^ 1677 := Nat.pow_le_pow_left (by norm_num) 1677
      _ = 15 ^ 16770 := by rw [show (16770 : ℕ) = 10 * 1677 from by norm_num, pow_mul]
  have hprod :
      (2 : ℕ) ^ 65403 * 2 ^ 245357 < 15 ^ 16770 * Nat.choose 245374 122687 := by
    calc
      (2 : ℕ) ^ 65403 * 2 ^ 245357 ≤ 15 ^ 16770 * 2 ^ 245357 :=
        Nat.mul_le_mul_right _ h15
      _ < 15 ^ 16770 * Nat.choose 245374 122687 :=
        Nat.mul_lt_mul_of_pos_left two_pow_lt_central_choose (by positivity)
  have hscaled :
      (2 : ℕ) ^ 50310 * 2 ^ 260338 < 2 ^ 50310 * Nat.choose 262144 122687 := by
    calc
      (2 : ℕ) ^ 50310 * 2 ^ 260338 = 2 ^ 310648 := by
        rw [show (310648 : ℕ) = 50310 + 260338 from by norm_num, pow_add]
      _ < 2 ^ 310760 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = 2 ^ 65403 * 2 ^ 245357 := by
        rw [show (310760 : ℕ) = 65403 + 245357 from by norm_num, pow_add]
      _ < 15 ^ 16770 * Nat.choose 245374 122687 := hprod
      _ ≤ 8 ^ 16770 * Nat.choose 262144 122687 := hgrowth
      _ = 2 ^ 50310 * Nat.choose 262144 122687 := by
        rw [show (8 : ℕ) = 2 ^ 3 from by norm_num, ← pow_mul,
          show (3 * 16770 : ℕ) = 50310 from by norm_num]
  exact Nat.lt_of_mul_lt_mul_left hscaled

theorem two_pow_lt_card : 2 ^ 260338 < Fintype.card CandidateSets := by
  rw [card_candidateSets]
  have hsymm : Nat.choose 262144 122687 = Nat.choose 262144 agreement := by
    change Nat.choose 262144 122687 = Nat.choose 262144 139457
    exact Nat.choose_symm_of_eq_add (by norm_num)
  rw [← hsymm]; exact two_pow_lt_choose

theorem pigeonhole_bound :
    Fintype.card (Fin signatureWidth → BF) * (Fintype.card F - 1) ^ 2 <
      Fintype.card CandidateSets :=
  signature_sieve_lt.trans two_pow_lt_card

/-! ## Popular base-signature fiber -/

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

theorem exists_baseSig_fiber :
    ∃ y : Fin signatureWidth → BF,
      (Fintype.card F - 1) ^ 2 <
        (Finset.univ.filter fun T : CandidateSets => baseSig T = y).card :=
  exists_large_fiber baseSig ((Fintype.card F - 1) ^ 2) pigeonhole_bound

noncomputable def chosenBaseSig : Fin signatureWidth → BF :=
  Classical.choose exists_baseSig_fiber

noncomputable def fiberSets : Finset CandidateSets :=
  Finset.univ.filter fun T => baseSig T = chosenBaseSig

abbrev FiberSets := ↥fiberSets

theorem card_fiberSets_large :
    (Fintype.card F - 1) ^ 2 < Fintype.card FiberSets := by
  rw [Fintype.card_coe]
  exact Classical.choose_spec exists_baseSig_fiber

theorem fiberSets_nonempty : fiberSets.Nonempty := by
  apply Finset.card_pos.mp
  rw [← Fintype.card_coe]
  exact lt_of_le_of_lt (Nat.zero_le _) card_fiberSets_large

noncomputable def anchor : FiberSets :=
  ⟨Classical.choose fiberSets_nonempty, Classical.choose_spec fiberSets_nonempty⟩

theorem member_baseSig (T : FiberSets) : baseSig T.1 = chosenBaseSig :=
  (Finset.mem_filter.mp T.2).2

/-- Members share the extension signature — the fact the degree drop consumes. -/
theorem member_signature (T : FiberSets) :
    signature T.1 = fun i => φ (chosenBaseSig i) := by
  funext i
  rw [signature_eq_map, member_baseSig]

/-! ## The SubHalfPigeonhole engine, verbatim -/

noncomputable def diffPoly (T : FiberSets) : Polynomial F :=
  rootPoly anchor.1 - rootPoly T.1

theorem diffPoly_degree_lt (T : FiberSets) :
    (diffPoly T).degree < (rowK : Nat) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [diffPoly, Polynomial.coeff_sub]
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
        (rootPoly_natDegree anchor.1 ▸ hgt),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (rootPoly_natDegree T.1 ▸ hgt), sub_zero]

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
  classical
  rw [rootPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := Benchmark.IRSProfile.domain j)
  · simp [nodes, hj]
  · simp

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
    simp only [fixedWord, if_pos, diffPoly, Polynomial.eval_sub]
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
  have hval : A.1 ≠ B.1 := fun h => hne (Subtype.ext h)
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
      exact hiB (by rwa [← heq] at hiUnion)
    have hlt := Finset.card_lt_card hBstrict
    simpa only [Set.powersetCard.card_eq B.1] using hlt
  apply no_message_agrees_on_more_than_agreement
    (message A) ((A.1 : Finset I) ∪ (B.1 : Finset I)) hcardUnion
  intro j hj
  rcases Finset.mem_union.mp hj with hjA | hjB
  · exact fixedWord_agrees A j hjA
  · rw [hAB]; exact fixedWord_agrees B j hjB

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
  · have hlt : (δ : ℝ) < 131073 / 262144 := by exact_mod_cast hδ.2
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
  · intro T; exact T.1.prop
  · exact fixedWord_agrees
  · exact message_eq_zero_of_zero_on_many

end IRSProfile
end ProximityPrize.SubmissionUpper.SubHalfBaseField
