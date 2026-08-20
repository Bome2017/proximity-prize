/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetUpper

/-!
# Subset-pigeonhole list-decoding lower bound for the squared IRS code

A re-parameterized port of the `DirectM0.lean` construction to the challenge's IRS profile
(`n = 2^18`, rate `1/2`, field `KoalaBear.Ext6`, squared interleaving `Fin 2 → Fin 8`).

Among the `C(2^18, 139502)` subsets `T` of the evaluation domain, at least `2^59` share the
same top `8430` coefficients of the vanishing polynomial `QFp T = ∏_{c ∈ T} (X − domain c)`
(those coefficients are Frobenius-fixed, hence lie in the prime field `ZMod 2130706433`, so
there are at most `p^8430` tuples — the count `2^59 * p^8430 ≤ C(262144, 139502)` is taken as
the hypothesis `hcount`). Matched tops make `QFp T0 − QFp T` a polynomial of degree
`≤ 131071 < 2^17`, i.e. an RS codeword of the base dimension, agreeing with the pivot word
`eval(QFp T0)` exactly on the `139502` roots of `QFp T` — relative Hamming distance
`122642/262144`. Diagonal stacking `w ↦ fun i a b ↦ w i` embeds these words into the squared
code `IRSProfile.code ^⋈ Fin 2` at the same distance, yielding a list of size `≥ 2^59` inside
the `122642/262144`-ball around the stacked pivot.

Every object is an abstract `Finset` product/image; no proof step scales with the subset size
`139502`.
-/

namespace ProximityPrize.SubmissionUpper

open ProximityPrize.Benchmark
open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Field characteristic facts over `IRSProfile.Field = KoalaBear.Ext6` -/

lemma fieldSize_eq : KoalaBear.fieldSize = 2130706433 := by
  norm_num [KoalaBear.fieldSize]

lemma prime_koala : Nat.Prime 2130706433 := fieldSize_eq ▸ KoalaBear.is_prime

lemma charP_ext6 : CharP IRSProfile.Field 2130706433 := by
  have hZ : CharP KoalaBear.Field 2130706433 :=
    fieldSize_eq ▸ (inferInstance : CharP KoalaBear.Field KoalaBear.fieldSize)
  exact (Algebra.charP_iff KoalaBear.Field IRSProfile.Field 2130706433).mp hZ

lemma expChar_ext6 : ExpChar IRSProfile.Field 2130706433 := by
  haveI := charP_ext6
  exact ExpChar.prime prime_koala

/-- Every domain point is fixed by the prime-power Frobenius: it lies in the prime field. -/
lemma domain_pow_p (i : IRSProfile.Index) :
    (IRSProfile.domain i) ^ 2130706433 = IRSProfile.domain i := by
  have h : (IRSProfile.baseNttDomain.node i) ^ 2130706433 = IRSProfile.baseNttDomain.node i :=
    fieldSize_eq ▸ ZMod.pow_card _
  show (CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i)) ^ 2130706433
      = CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i)
  rw [← CompPoly.Extension.Ext.ofBaseRingHom_apply, ← map_pow, h]

/-- The prime-fixed points of the sextic field number at most `p`. -/
lemma fixedField_card_le :
    (Finset.univ.filter (fun y : IRSProfile.Field => y ^ 2130706433 = y)).card
      ≤ 2130706433 := by
  classical
  haveI : Fact (Nat.Prime 2130706433) := ⟨prime_koala⟩
  haveI := charP_ext6
  have heq : (Finset.univ.filter (fun y : IRSProfile.Field => y ^ 2130706433 = y))
      = (Finset.univ.filter
          (fun y : IRSProfile.Field => y ∈ (⊥ : Subfield IRSProfile.Field))) :=
    Finset.filter_congr (fun y _ => by
      rw [Subfield.mem_bot_iff_pow_eq_self IRSProfile.Field 2130706433])
  rw [heq]
  refine le_of_eq ?_
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Subfield.card_bot]

/-! ### The vanishing polynomial and its prime-field top coefficients -/

/-- The vanishing polynomial of a subset `T` of the domain index. -/
def QFp (T : Finset IRSProfile.Index) : Polynomial IRSProfile.Field :=
  ∏ c ∈ T, (Polynomial.X - Polynomial.C (IRSProfile.domain c))

/-- Every coefficient of `QFp T` is Frobenius-fixed: the roots all lie in the prime field. -/
lemma QFp_coeff_fixed (T : Finset IRSProfile.Index) (j : ℕ) :
    ((QFp T).coeff j) ^ 2130706433 = (QFp T).coeff j := by
  haveI := expChar_ext6
  have hmap : (QFp T).map (frobenius IRSProfile.Field 2130706433) = QFp T := by
    rw [QFp, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, frobenius_def, domain_pow_p]
  calc ((QFp T).coeff j) ^ 2130706433
      = (frobenius IRSProfile.Field 2130706433) ((QFp T).coeff j) := (frobenius_def _ _).symm
    _ = ((QFp T).map (frobenius IRSProfile.Field 2130706433)).coeff j :=
        (Polynomial.coeff_map _ _).symm
    _ = (QFp T).coeff j := by rw [hmap]

/-! ### The pigeonhole fiber: `≥ 2^59` subsets sharing `8430` top coefficients -/

/-- The prime subfield, as a `Finset`. -/
def fixedField : Finset IRSProfile.Field :=
  Finset.univ.filter (fun y => y ^ 2130706433 = y)

lemma mem_fixedField {y : IRSProfile.Field} :
    y ∈ fixedField ↔ y ^ 2130706433 = y := by
  simp [fixedField]

lemma fixedField_nonempty : fixedField.Nonempty :=
  ⟨0, by rw [mem_fixedField]; exact zero_pow (by norm_num)⟩

/-- The matched top coefficients: indices `131072 + i` for `i < 8430`. -/
def coeffTup (T : Finset IRSProfile.Index) : Fin 8430 → IRSProfile.Field :=
  fun i => (QFp T).coeff (131072 + (i : ℕ))

/-- The coefficient-tuple cells: at most `p^8430` of them. -/
def cellFp : Finset (Fin 8430 → IRSProfile.Field) :=
  Fintype.piFinset (fun _ => fixedField)

/-- Pigeonhole: some coefficient tuple is shared by at least `2^59` of the
`C(2^18, 139502)` subsets. -/
lemma exists_fiber (hcount : 2 ^ 59 * 2130706433 ^ 8430 ≤ Nat.choose 262144 139502) :
    ∃ v : Fin 8430 → IRSProfile.Field, v ∈ cellFp ∧
      2 ^ 59 ≤ (((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).filter
        (fun T => coeffTup T = v)).card := by
  classical
  have hs : ((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).card
      = Nat.choose 262144 139502 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      show (2 : ℕ) ^ 18 = 262144 from by norm_num1]
  have hmaps : ∀ T ∈ (Finset.univ : Finset IRSProfile.Index).powersetCard 139502,
      coeffTup T ∈ cellFp := by
    intro T _
    rw [cellFp, Fintype.mem_piFinset]
    exact fun i => mem_fixedField.mpr (QFp_coeff_fixed T (131072 + (i : ℕ)))
  have ht : cellFp.Nonempty := Fintype.piFinset_nonempty.mpr fun _ => fixedField_nonempty
  have hcard : cellFp.card ≤ 2130706433 ^ 8430 := by
    rw [cellFp, Fintype.card_piFinset]
    calc (∏ _i : Fin 8430, fixedField.card) = fixedField.card ^ 8430 := by
          simp [Finset.prod_const]
      _ ≤ 2130706433 ^ 8430 := Nat.pow_le_pow_left fixedField_card_le 8430
  have hsum : ((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).card
      = ∑ v ∈ cellFp, (((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).filter
          (fun T => coeffTup T = v)).card :=
    Finset.card_eq_sum_card_fiberwise fun T hT => hmaps T hT
  have hle : ∑ _v ∈ cellFp, 2 ^ 59
      ≤ ∑ v ∈ cellFp, (((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).filter
          (fun T => coeffTup T = v)).card := by
    rw [← hsum, hs]
    calc ∑ _v ∈ cellFp, 2 ^ 59 = cellFp.card * 2 ^ 59 := by
          simp [Finset.sum_const, smul_eq_mul]
      _ ≤ 2130706433 ^ 8430 * 2 ^ 59 := Nat.mul_le_mul_right _ hcard
      _ = 2 ^ 59 * 2130706433 ^ 8430 := by ring
      _ ≤ Nat.choose 262144 139502 := hcount
  obtain ⟨v, hv, hvle⟩ := Finset.exists_le_of_sum_le ht hle
  exact ⟨v, hv, hvle⟩

/-! ### Matching `8430` top coefficients drops the difference degree below `2^17` -/

lemma QFp_monic (T : Finset IRSProfile.Index) : (QFp T).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)

lemma QFp_natDegree (T : Finset IRSProfile.Index) : (QFp T).natDegree = T.card := by
  rw [QFp, Polynomial.natDegree_prod _ _ (fun c _ => Polynomial.X_sub_C_ne_zero _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

lemma QFp_sub_natDegree_le {T T0 : Finset IRSProfile.Index} (hT : T.card = 139502)
    (hT0 : T0.card = 139502) (hc : coeffTup T = coeffTup T0) :
    (QFp T0 - QFp T).natDegree ≤ 131071 := by
  have key : ∀ j, 131072 ≤ j → j ≤ 139501 → (QFp T).coeff j = (QFp T0).coeff j := by
    intro j hj1 hj2
    have hjlt : j - 131072 < 8430 := by omega
    have h : (QFp T).coeff (131072 + (j - 131072))
        = (QFp T0).coeff (131072 + (j - 131072)) :=
      congrFun hc ⟨j - 131072, hjlt⟩
    rwa [show 131072 + (j - 131072) = j from by omega] at h
  have hnd0 : (QFp T0).natDegree = 139502 := by rw [QFp_natDegree, hT0]
  have hnd : (QFp T).natDegree = 139502 := by rw [QFp_natDegree, hT]
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [Polynomial.coeff_sub]
  by_cases hle : j ≤ 139501
  · rw [key j (by omega) hle, sub_self]
  · rcases eq_or_lt_of_le (show 139502 ≤ j by omega) with heq | hgt
    · have c0 : (QFp T0).coeff 139502 = 1 := by
        rw [← hnd0]; exact (QFp_monic T0).coeff_natDegree
      have c1 : (QFp T).coeff 139502 = 1 := by
        rw [← hnd]; exact (QFp_monic T).coeff_natDegree
      rw [← heq, c0, c1, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hnd0]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hnd]; omega), sub_self]

/-! ### Roots of `QFp T` and the pivot/difference words -/

/-- `QFp T` vanishes at `domain i` iff `i ∈ T` (`domain` is injective). -/
lemma eval_QFp_eq_zero_iff (T : Finset IRSProfile.Index) (i : IRSProfile.Index) :
    (QFp T).eval (IRSProfile.domain i) = 0 ↔ i ∈ T := by
  rw [QFp, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  constructor
  · rintro ⟨c, hc, hdc⟩
    obtain rfl := IRSProfile.domain.injective hdc
    exact hc
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- The pivot word: evaluation of `QFp T0` on the domain. -/
def powWord (T0 : Finset IRSProfile.Index) : IRSProfile.Index → IRSProfile.Field :=
  fun i => (QFp T0).eval (IRSProfile.domain i)

/-- The difference word: evaluation of `QFp T0 − QFp T` on the domain. -/
def cword (T0 T : Finset IRSProfile.Index) : IRSProfile.Index → IRSProfile.Field :=
  fun i => powWord T0 i - (QFp T).eval (IRSProfile.domain i)

/-- The difference word of two matched subsets is a base RS codeword (degree `< 2^17`). -/
lemma cword_mem_rsCode {T0 T : Finset IRSProfile.Index} (hT : T.card = 139502)
    (hT0 : T0.card = 139502) (hcoeff : coeffTup T = coeffTup T0) :
    cword T0 T ∈ ReedSolomon.code IRSProfile.domain 131072 := by
  have hdeg : (QFp T0 - QFp T).natDegree < 131072 :=
    Nat.lt_of_le_of_lt (QFp_sub_natDegree_le hT hT0 hcoeff) (by norm_num)
  show cword T0 T ∈ (Polynomial.degreeLT IRSProfile.Field 131072).map
    (ReedSolomon.evalOnPoints IRSProfile.domain)
  refine Submodule.mem_map.mpr ⟨QFp T0 - QFp T, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLT]
    rcases eq_or_ne (QFp T0 - QFp T) 0 with h0 | h0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp hdeg
  · funext i
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, cword, powWord,
      Polynomial.eval_sub]

/-! ### Diagonal stacking into the squared interleaved code -/

/-- The diagonal stack of a base word into the squared code's word type. -/
def stack (w : IRSProfile.Index → IRSProfile.Field) :
    IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field := fun i _ _ => w i

/-- Membership in the squared code, row-wise. -/
lemma mem_squCode_iff (V : IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field) :
    V ∈ ((IRSProfile.code ^⋈ (Fin 2)) : ModuleCode IRSProfile.Index IRSProfile.Field
        (Fin 2 → Fin 8 → IRSProfile.Field)) ↔
      ∀ a : Fin 2, (fun i => V i a) ∈ IRSProfile.code := Iff.rfl

/-- Membership in the interleaved code, column-wise. -/
lemma mem_code_iff (W : IRSProfile.Index → Fin 8 → IRSProfile.Field) :
    W ∈ IRSProfile.code ↔
      ∀ b : Fin 8, (fun i => W i b) ∈ ReedSolomon.code IRSProfile.domain 131072 := by
  have h1 : W ∈ IRSProfile.code ↔ ∀ b : Fin 8, (fun i => W i b) ∈
      ReedSolomon.code IRSProfile.domain
        (IRSProfile.totalDimension / IRSProfile.interleaving) := Iff.rfl
  rwa [show IRSProfile.totalDimension / IRSProfile.interleaving = 131072 from by
    norm_num [IRSProfile.totalDimension, IRSProfile.interleaving]] at h1

/-- The diagonal stack of a base codeword lies in the squared code. -/
lemma stack_mem_squCode {w : IRSProfile.Index → IRSProfile.Field}
    (hw : w ∈ ReedSolomon.code IRSProfile.domain 131072) :
    stack w ∈ (((IRSProfile.code ^⋈ (Fin 2)) : ModuleCode IRSProfile.Index IRSProfile.Field
        (Fin 2 → Fin 8 → IRSProfile.Field)) : Set _) :=
  SetLike.mem_coe.mpr ((mem_squCode_iff (stack w)).mpr
    fun a => (mem_code_iff (fun i => stack w i a)).mpr fun _ => hw)

/-- Stacking preserves the Hamming distance: the disagreement sets coincide. -/
lemma hammingDist_stack (x y : IRSProfile.Index → IRSProfile.Field) :
    hammingDist (stack x) (stack y) = hammingDist x y := by
  rw [Code.hammingDist_eq_disagreementCols_card, Code.hammingDist_eq_disagreementCols_card]
  congr 1
  ext i
  simp only [Code.mem_disagreementCols, ne_eq, stack]
  constructor
  · intro h hxy
    exact h (funext fun a => funext fun b => hxy)
  · intro h hxy
    exact h (congrFun (congrFun hxy 0) 0)

/-- The distance from the pivot to the difference word is exactly `122642/262144`:
they agree exactly on the `139502` roots of `QFp T`. -/
lemma cword_dist (T0 T : Finset IRSProfile.Index) (hT : T.card = 139502) :
    δᵣ(stack (powWord T0), stack (cword T0 T)) = (122642 / 262144 : ℚ≥0) := by
  classical
  have hagree : (Finset.univ.filter (fun i : IRSProfile.Index =>
      powWord T0 i = cword T0 T i)).card = 139502 := by
    have heq : (Finset.univ.filter (fun i : IRSProfile.Index =>
        powWord T0 i = cword T0 T i)) = T := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cword, powWord]
      rw [eq_comm, sub_eq_self, eval_QFp_eq_zero_iff]
    rw [heq, hT]
  have hdis : hammingDist (stack (powWord T0)) (stack (cword T0 T)) = 122642 := by
    rw [hammingDist_stack, Code.hammingDist_eq_disagreementCols_card]
    have huniv : (Finset.univ : Finset IRSProfile.Index).card = 262144 := by
      rw [Finset.card_univ, Fintype.card_fin, show (2 : ℕ) ^ 18 = 262144 from by norm_num1]
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset IRSProfile.Index))
      (p := fun i => powWord T0 i = cword T0 T i)
    rw [hagree, huniv] at hsum
    have hfilt : Code.disagreementCols (powWord T0) (cword T0 T)
        = Finset.univ.filter (fun i => ¬ powWord T0 i = cword T0 T i) := by
      ext i; simp [Code.mem_disagreementCols]
    rw [hfilt]
    omega
  have hcardI : Fintype.card IRSProfile.Index = 262144 := by
    rw [Fintype.card_fin]; norm_num1
  rw [Code.relHammingDist, hdis, hcardI]
  norm_num [NNRat.cast_natCast]

/-- Stacked difference words determine the subset: the root set is recovered from the
agreement set with the pivot, and `domain` is injective. -/
lemma stack_cword_inj {T0 T T' : Finset IRSProfile.Index}
    (h : stack (cword T0 T) = stack (cword T0 T')) : T = T' := by
  have hcw : cword T0 T = cword T0 T' :=
    funext fun i => congrFun (congrFun (congrFun h i) 0) 0
  have hev : ∀ i, (QFp T).eval (IRSProfile.domain i)
      = (QFp T').eval (IRSProfile.domain i) := by
    intro i
    have hi := congrFun hcw i
    simp only [cword, powWord] at hi
    exact sub_right_inj.mp hi
  ext i
  rw [← eval_QFp_eq_zero_iff T i, ← eval_QFp_eq_zero_iff T' i, hev i]

/-! ### The large list inside the `122642/262144`-ball -/

/-- The subset-pigeonhole list lower bound at radius `122642/262144` for the squared IRS
code: at least `2^59` squared codewords lie that close to the stacked pivot word. -/
theorem exists_large_squared_list
    (hcount : 2 ^ 59 * 2130706433 ^ 8430 ≤ Nat.choose 262144 139502) :
    ∃ (fStar : IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field)
      (S : Finset (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field)),
      2 ^ 59 ≤ S.card ∧
      ∀ V ∈ S, V ∈ Code.closeCodewordsRel
        (((IRSProfile.code ^⋈ (Fin 2)) : ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin 8 → IRSProfile.Field)) : Set _)
        fStar ((122642 / 262144 : ℝ≥0) : ℝ) := by
  classical
  obtain ⟨v, -, hcard⟩ := exists_fiber hcount
  set fiber := ((Finset.univ : Finset IRSProfile.Index).powersetCard 139502).filter
    (fun T => coeffTup T = v) with hfiber
  have hfne : fiber.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hcard)
  obtain ⟨T0, hT0mem⟩ := hfne
  have hT0f := Finset.mem_filter.mp hT0mem
  have hT0card : T0.card = 139502 := (Finset.mem_powersetCard.mp hT0f.1).2
  refine ⟨stack (powWord T0), fiber.image (fun T => stack (cword T0 T)), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (fun T _ T' _ h => stack_cword_inj h)]
    exact hcard
  · intro V hV
    rw [Finset.mem_image] at hV
    obtain ⟨T, hTmem, rfl⟩ := hV
    have hTf := Finset.mem_filter.mp hTmem
    have hTcard : T.card = 139502 := (Finset.mem_powersetCard.mp hTf.1).2
    have hcoeff : coeffTup T = coeffTup T0 := by rw [hTf.2, hT0f.2]
    rw [Code.mem_closeCodewordsRel_iff]
    refine ⟨stack_mem_squCode (cword_mem_rsCode hTcard hT0card hcoeff), ?_⟩
    rw [cword_dist T0 T hTcard]
    apply le_of_eq
    norm_num [NNRat.cast_div, NNRat.cast_natCast, NNReal.coe_div]

end ProximityPrize.SubmissionUpper
