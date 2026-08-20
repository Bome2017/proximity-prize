/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.MultiAnchorCombinatorics

namespace ProximityPrize.SubmissionUpper.MultiAnchor

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped BigOperators NNReal ProbabilityTheory

set_option maxRecDepth 100000

namespace IRSProfile

open ProximityPrize.Benchmark

abbrev k := Benchmark.IRSProfile.totalDimension
abbrev s := Benchmark.IRSProfile.interleaving

local instance : NeZero s := ⟨by norm_num [s, Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = rowK :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [rowK, Benchmark.IRSProfile.baseDimension])

theorem chosenSets_nonempty : chosenSets.Nonempty := by
  apply Finset.card_pos.mp
  rw [chosenSets_card]
  norm_num [familySize]

noncomputable def baseSet : ChosenSets :=
  ⟨Classical.choose chosenSets_nonempty, Classical.choose_spec chosenSets_nonempty⟩

noncomputable def diffPoly (T : CandidateSets) : Polynomial F :=
  rootPoly T - rootPoly baseSet.1

theorem chosen_rootPoly_eval_zero_eq (T : ChosenSets) :
    (rootPoly T.1).eval 0 = (rootPoly baseSet.1).eval 0 := by
  calc
    (rootPoly T.1).eval 0 = (rootPoly T.1).eval (emb 0) := by rw [map_zero]
    _ = emb ((rootPolyK T.1).eval 0) := by simp [rootPoly]
    _ = emb ((rootPolyK baseSet.1).eval 0) :=
      congrArg emb (chosen_eval_zero_eq T baseSet)
    _ = (rootPoly baseSet.1).eval (emb 0) := by simp [rootPoly]
    _ = (rootPoly baseSet.1).eval 0 := by rw [map_zero]

theorem chosen_rootPoly_eval_anchor_eq (T : ChosenSets) (i : Fin anchorCount) :
    (rootPoly T.1).eval (emb (anchorNode i)) =
      (rootPoly baseSet.1).eval (emb (anchorNode i)) := by
  simpa [rootPoly, Polynomial.eval_map, Polynomial.eval₂_hom] using
    congrArg emb (chosen_eval_anchor_eq T baseSet i)

theorem diffPoly_eval_fixedPoint (T : ChosenSets) (a : F) (ha : a ∈ fixedPoints) :
    (diffPoly T.1).eval a = 0 := by
  rw [fixedPoints, Finset.mem_insert] at ha
  rcases ha with rfl | ha
  · simp only [diffPoly, Polynomial.eval_sub, chosen_rootPoly_eval_zero_eq, sub_self]
  · rw [anchorNodesF, Finset.mem_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    simp only [diffPoly, Polynomial.eval_sub, chosen_rootPoly_eval_anchor_eq, sub_self]

lemma finset_prod_X_sub_C_dvd_of_eval_eq_zero
    (S : Finset F) (p : Polynomial F) (h : ∀ a ∈ S, p.eval a = 0) :
    (S.prod fun a => Polynomial.X - Polynomial.C a) ∣ p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp S.1]
  exact Finset.val_le_iff_val_subset.mpr fun a ha =>
    (Polynomial.mem_roots hp).2 (by simpa [Polynomial.IsRoot.def] using h a ha)

theorem W0_dvd_diffPoly (T : ChosenSets) : W0 ∣ diffPoly T.1 := by
  exact finset_prod_X_sub_C_dvd_of_eval_eq_zero fixedPoints (diffPoly T.1)
    (diffPoly_eval_fixedPoint T)

noncomputable def quotientPoly (T : CandidateSets) : Polynomial F :=
  diffPoly T /ₘ W0

theorem W0_mul_quotientPoly (T : ChosenSets) :
    W0 * quotientPoly T.1 = diffPoly T.1 := by
  have hmod : diffPoly T.1 %ₘ W0 = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd W0_monic).2 (W0_dvd_diffPoly T)
  have hdiv := Polynomial.modByMonic_add_div (diffPoly T.1) W0
  rw [hmod, zero_add] at hdiv
  exact hdiv

noncomputable def challenge (T : CandidateSets) : F :=
  (quotientPoly T).eval lambda

noncomputable def remainderPoly (T : CandidateSets) : Polynomial F :=
  (quotientPoly T - Polynomial.C (challenge T)) /ₘ
    (Polynomial.X - Polynomial.C lambda)

theorem X_sub_lambda_mul_remainderPoly (T : CandidateSets) :
    (Polynomial.X - Polynomial.C lambda) * remainderPoly T =
      quotientPoly T - Polynomial.C (challenge T) := by
  rw [remainderPoly, Polynomial.mul_divByMonic_eq_iff_isRoot]
  simp [Polynomial.IsRoot.def, challenge]

noncomputable def W : Polynomial F :=
  W0 * (Polynomial.X - Polynomial.C lambda)

theorem W_monic : W.Monic := W0_monic.mul (Polynomial.monic_X_sub_C lambda)

theorem W_natDegree : W.natDegree = 16 := by
  rw [W, Polynomial.natDegree_mul W0_monic.ne_zero (Polynomial.monic_X_sub_C lambda).ne_zero,
    W0_natDegree, Polynomial.natDegree_X_sub_C]
  norm_num

theorem locator_pencil (T : ChosenSets) :
    rootPoly T.1 = rootPoly baseSet.1 + Polynomial.C (challenge T.1) * W0 +
      W * remainderPoly T.1 := by
  have hD := W0_mul_quotientPoly T
  have hV := X_sub_lambda_mul_remainderPoly T.1
  rw [diffPoly] at hD
  rw [W]
  linear_combination hD + W0 * hV

theorem challenge_injective :
    Function.Injective (fun T : ChosenSets => challenge T.1) := by
  intro A B hAB
  apply eval_lambda_injective
  have hPA := congrArg (fun p : Polynomial F => p.eval lambda) (locator_pencil A)
  have hPB := congrArg (fun p : Polynomial F => p.eval lambda) (locator_pencil B)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, W,
    Polynomial.eval_sub, Polynomial.eval_X, sub_self, mul_zero, zero_mul, add_zero] at hPA hPB
  rw [hAB] at hPA
  exact hPA.trans hPB.symm

theorem diffPoly_natDegree_le (T : CandidateSets) : (diffPoly T).natDegree ≤ 271 :=
  rootPoly_sub_natDegree_le T baseSet.1

theorem quotientPoly_natDegree_le (T : CandidateSets) :
    (quotientPoly T).natDegree ≤ 256 := by
  have hdeg := diffPoly_natDegree_le T
  rw [quotientPoly, Polynomial.natDegree_divByMonic _ W0_monic, W0_natDegree]
  omega

theorem remainderPoly_natDegree_le (T : CandidateSets) :
    (remainderPoly T).natDegree ≤ 255 := by
  rw [remainderPoly, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C lambda),
    Polynomial.natDegree_X_sub_C]
  have hsub : (quotientPoly T - Polynomial.C (challenge T)).natDegree ≤ 256 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by
      rw [Polynomial.natDegree_C]
      exact max_le (quotientPoly_natDegree_le T) (by omega))
  omega

theorem fixedPoint_not_mem_quotientNodesF {a : F} (ha : a ∈ fixedPoints) :
    a ∉ quotientNodesF := by
  intro hq
  rw [quotientNodesF, Finset.mem_image] at hq
  obtain ⟨r, -, hr⟩ := hq
  rw [fixedPoints, Finset.mem_insert] at ha
  rcases ha with rfl | ha
  · have hz : zeta ^ r.1 ≠ 0 := pow_ne_zero _
      (zeta_primitive.ne_zero (by norm_num [quotientSize]))
    exact hz (emb_injective (by simpa using hr))
  · rw [anchorNodesF, Finset.mem_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact anchorNode_ne_quotient i r (emb_injective hr).symm

theorem W0_eval_ne_zero_of_mem_quotientNodesF {y : F} (hy : y ∈ quotientNodesF) :
    W0.eval y ≠ 0 := by
  rw [W0, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
  exact fun h => fixedPoint_not_mem_quotientNodesF ha (h ▸ hy)

abbrev blockEquiv : Fin 512 × Fin 512 ≃ I :=
  finProdFinEquiv

def blockIndex (q r : Fin 512) : I :=
  blockEquiv (q, r)

theorem domain_blockIndex_pow (q r : Fin 512) :
    Benchmark.IRSProfile.domain (blockIndex q r) ^ fiberSize = emb (zeta ^ r.1) := by
  change (emb (D.node (blockIndex q r))) ^ fiberSize = emb (zeta ^ r.1)
  rw [← map_pow emb]
  congr 1
  change (omega ^ (r.1 + 512 * q.1)) ^ 512 = (omega ^ 512) ^ r.1
  calc
    (omega ^ (r.1 + 512 * q.1)) ^ 512 =
        omega ^ (512 * r.1 + 262144 * q.1) := by
      rw [pow_mul]
      congr 1
      omega
    _ = omega ^ (512 * r.1) * (omega ^ 262144) ^ q.1 := by
      rw [pow_add, pow_mul]
    _ = omega ^ (512 * r.1) := by
      have hroot : omega ^ 262144 = 1 := by
        simpa [D, Benchmark.IRSProfile.baseNttDomain] using D.primitive.pow_eq_one
      rw [hroot, one_pow, mul_one]
    _ = (omega ^ 512) ^ r.1 := by rw [pow_mul]

theorem domain_pow_mem_quotientNodesF (j : I) :
    Benchmark.IRSProfile.domain j ^ fiberSize ∈ quotientNodesF := by
  let qr : Fin 512 × Fin 512 := blockEquiv.symm j
  have hj : j = blockIndex qr.1 qr.2 := by
    exact (blockEquiv.apply_symm_apply j).symm
  rw [hj, domain_blockIndex_pow]
  simp [quotientNodesF]

theorem W_eval_domain_pow_ne_zero (j : I) :
    W.eval (Benchmark.IRSProfile.domain j ^ fiberSize) ≠ 0 := by
  have hy := domain_pow_mem_quotientNodesF j
  have h0 := W0_eval_ne_zero_of_mem_quotientNodesF hy
  have hlambda : Benchmark.IRSProfile.domain j ^ fiberSize ≠ lambda := by
    intro h
    exact lambda_not_mem_quotientNodesF (h ▸ hy)
  simp only [W, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, mul_ne_zero_iff]
  exact ⟨h0, sub_ne_zero.mpr hlambda⟩

def padIndex (q : Fin 511) : I :=
  blockIndex ⟨q.1, by omega⟩ 0

theorem padIndex_injective : Function.Injective padIndex := by
  intro a b h
  change blockEquiv
      ((⟨a.1, by omega⟩ : Fin 512), (0 : Fin 512)) =
    blockEquiv ((⟨b.1, by omega⟩ : Fin 512), (0 : Fin 512)) at h
  have hp := blockEquiv.injective h
  exact Fin.ext (congrArg (fun x => x.1.1) hp)

noncomputable def padNodes : Finset F :=
  Finset.univ.image fun q : Fin 511 => Benchmark.IRSProfile.domain (padIndex q)

theorem padNodes_card : padNodes.card = 511 := by
  rw [padNodes, Finset.card_image_of_injective]
  · simp
  · exact Benchmark.IRSProfile.domain.injective.comp padIndex_injective

noncomputable def padPoly : Polynomial F :=
  padNodes.prod fun a => Polynomial.X - Polynomial.C a

theorem padPoly_monic : padPoly.Monic := by
  simpa only [padPoly] using Polynomial.monic_prod_X_sub_C (fun a : F => a) padNodes

theorem padPoly_natDegree : padPoly.natDegree = 511 := by
  rw [padPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, padNodes_card]

theorem padPoly_eval_padIndex (q : Fin 511) :
    padPoly.eval (Benchmark.IRSProfile.domain (padIndex q)) = 0 := by
  rw [padPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := Benchmark.IRSProfile.domain (padIndex q))
  · simp [padNodes]
      · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

def rootIndexPair (iq : Fin 511 × Fin 512) : I :=
  blockIndex iq.2 ⟨iq.1.1 + 1, by omega⟩

theorem rootIndexPair_injective : Function.Injective rootIndexPair := by
  intro a b h
  change blockEquiv (a.2, (⟨a.1.1 + 1, by omega⟩ : Fin 512)) =
    blockEquiv (b.2, (⟨b.1.1 + 1, by omega⟩ : Fin 512)) at h
  have hp := blockEquiv.injective h
  apply Prod.ext
  · apply Fin.ext
    have := congrArg (fun x => x.2.1) hp
    omega
  · exact congrArg Prod.fst hp

noncomputable def padIndices : Finset I :=
  Finset.univ.image padIndex

noncomputable def rootIndices (T : CandidateSets) : Finset I :=
  ((T.1 : Finset (Fin 511)).product (Finset.univ : Finset (Fin 512))).image rootIndexPair

noncomputable def agreementIndices (T : CandidateSets) : Finset I :=
  padIndices ∪ rootIndices T

theorem padIndices_card : padIndices.card = 511 := by
  rw [padIndices, Finset.card_image_of_injective]
  · simp
  · exact padIndex_injective

theorem rootIndices_card (T : CandidateSets) : (rootIndices T).card = locatorSize * fiberSize := by
  rw [rootIndices, Finset.card_image_of_injective _ rootIndexPair_injective]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, T.prop]

theorem padIndices_disjoint_rootIndices (T : CandidateSets) :
    Disjoint padIndices (rootIndices T) := by
  rw [Finset.disjoint_left]
  intro j hjp hjr
  rw [padIndices, Finset.mem_image] at hjp
  obtain ⟨q, -, rfl⟩ := hjp
  rw [rootIndices, Finset.mem_image] at hjr
  obtain ⟨ir, hir, heq⟩ := hjr
  change blockEquiv
      (ir.2, (⟨ir.1.1 + 1, by omega⟩ : Fin 512)) =
    blockEquiv
      ((⟨q.1, by omega⟩ : Fin 512), (0 : Fin 512)) at heq
  have hp := blockEquiv.injective heq
  have hs := congrArg (fun x => x.2.1) hp
  omega

theorem agreementIndices_card (T : CandidateSets) :
    (agreementIndices T).card = agreement := by
  rw [agreementIndices, Finset.card_union_of_disjoint (padIndices_disjoint_rootIndices T),
    padIndices_card, rootIndices_card]
  norm_num [agreement, locatorSize, fiberSize]

theorem padPoly_eval_zero_of_mem_padIndices (j : I) (hj : j ∈ padIndices) :
    padPoly.eval (Benchmark.IRSProfile.domain j) = 0 := by
  rw [padIndices, Finset.mem_image] at hj
  obtain ⟨q, -, rfl⟩ := hj
  exact padPoly_eval_padIndex q

theorem rootPoly_eval_zero_of_mem_rootIndices (T : CandidateSets) (j : I)
    (hj : j ∈ rootIndices T) :
    (rootPoly T).eval (Benchmark.IRSProfile.domain j ^ fiberSize) = 0 := by
  rw [rootIndices, Finset.mem_image] at hj
  obtain ⟨ir, hir, rfl⟩ := hj
  have hi : ir.1 ∈ (T.1 : Finset (Fin 511)) := (Finset.mem_product.mp hir).1
  rw [show rootIndexPair ir = blockIndex ir.2 ⟨ir.1.1 + 1, by omega⟩ by rfl,
    domain_blockIndex_pow]
  have hbase : (rootPolyK T).eval (locatorNode ir.1) = 0 := by
    rw [rootPolyK, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := ir.1)
    · exact hi
    · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  simpa [rootPoly] using congrArg emb hbase

noncomputable def codePoly (T : CandidateSets) : Polynomial F :=
  padPoly * (remainderPoly T).comp ((Polynomial.X : Polynomial F) ^ fiberSize)

theorem codePoly_natDegree_le (T : CandidateSets) : (codePoly T).natDegree ≤ 131071 := by
  calc
    (codePoly T).natDegree ≤ padPoly.natDegree +
        ((remainderPoly T).comp ((Polynomial.X : Polynomial F) ^ fiberSize)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 511 + (remainderPoly T).natDegree *
        ((Polynomial.X : Polynomial F) ^ fiberSize).natDegree := by
      rw [padPoly_natDegree]
      gcongr
      exact Polynomial.natDegree_comp_le
    _ ≤ 511 + 255 * 512 := by
      rw [Polynomial.natDegree_X_pow]
      gcongr
      exact remainderPoly_natDegree_le T
    _ = 131071 := by norm_num

theorem codePoly_degree_lt (T : CandidateSets) : (codePoly T).degree < (rowK : Nat) := by
  exact (Polynomial.degree_le_of_natDegree_le (codePoly_natDegree_le T)).trans_lt
    (by norm_num [rowK])

noncomputable def coeff (T : CandidateSets) : Fin (k / s) → F :=
  Polynomial.degreeLTEquiv F (k / s) ⟨codePoly T, by
    rw [Polynomial.mem_degreeLT]
    simpa only [rowDimension_eq] using codePoly_degree_lt T⟩

noncomputable def rows (T : CandidateSets) : Fin s → Fin (k / s) → F :=
  fun row => if row = 0 then coeff T else 0

noncomputable def message (T : CandidateSets) : Fin k → F :=
  flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension (rows T)

theorem rsPolynomial_coeff (T : CandidateSets) :
    ToyProblem.Spec.rsPolynomial (k / s) (coeff T) = codePoly T := by
  exact congrArg Subtype.val
    ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply
      ⟨codePoly T, by
        rw [Polynomial.mem_degreeLT]
        simpa only [rowDimension_eq] using codePoly_degree_lt T⟩)

theorem encoder_message_apply (T : CandidateSets) (j : I) (row : Fin s) :
    Benchmark.IRSProfile.encoder (message T) j row =
      if row = 0 then (codePoly T).eval (Benchmark.IRSProfile.domain j) else 0 := by
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension (message T) row) j = _
  rw [message, unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows T 0 = coeff T by simp [rows], ToyProblem.Spec.rsEncoder_apply,
      rsPolynomial_coeff]
    simp
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [rows, hrow] using hz

noncomputable def scalarWord0 (j : I) : F :=
  -(padPoly.eval (Benchmark.IRSProfile.domain j) *
      (rootPoly baseSet.1).eval (Benchmark.IRSProfile.domain j ^ fiberSize)) /
    W.eval (Benchmark.IRSProfile.domain j ^ fiberSize)

noncomputable def scalarWord1 (j : I) : F :=
  -(padPoly.eval (Benchmark.IRSProfile.domain j) *
      W0.eval (Benchmark.IRSProfile.domain j ^ fiberSize)) /
    W.eval (Benchmark.IRSProfile.domain j ^ fiberSize)

noncomputable def word0 : I → Fin s → F :=
  fun j row => if row = 0 then scalarWord0 j else 0

noncomputable def word1 : I → Fin s → F :=
  fun j row => if row = 0 then scalarWord1 j else 0

noncomputable def attackStack : Code.WordStack (Fin s → F) (Fin 2) I :=
  fun r => Fin.cases word0 (fun _ => word1) r

theorem scalar_fold_eq_codePoly_of_mem (T : ChosenSets) (j : I)
    (hj : j ∈ agreementIndices T.1) :
    scalarWord0 j + challenge T.1 * scalarWord1 j =
      (codePoly T.1).eval (Benchmark.IRSProfile.domain j) := by
  have hW := W_eval_domain_pow_ne_zero j
  rw [agreementIndices, Finset.mem_union] at hj
  rcases hj with hjpad | hjroot
  · have hA := padPoly_eval_zero_of_mem_padIndices j hjpad
    simp [scalarWord0, scalarWord1, codePoly, Polynomial.eval_mul, hA]
  · have hP := rootPoly_eval_zero_of_mem_rootIndices T.1 j hjroot
    have hpencil := congrArg
      (fun p : Polynomial F => p.eval (Benchmark.IRSProfile.domain j ^ fiberSize))
      (locator_pencil T)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hpencil
    rw [hP] at hpencil
    simp only [scalarWord0, scalarWord1, codePoly, Polynomial.eval_mul,
      Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    field_simp [hW]
    linear_combination -(padPoly.eval (Benchmark.IRSProfile.domain j)) * hpencil

theorem fold_agrees (T : ChosenSets) (j : I) (hj : j ∈ agreementIndices T.1) :
    (word0 + challenge T.1 • word1) j = Benchmark.IRSProfile.encoder (message T.1) j := by
  funext row
  rw [Pi.add_apply, Pi.smul_apply, encoder_message_apply]
  by_cases hrow : row = 0
  · subst row
    simpa [word0, word1, smul_eq_mul] using scalar_fold_eq_codePoly_of_mem T j hj
  · simp [word0, word1, hrow]

theorem encoder_message_mem_code (T : CandidateSets) :
    Benchmark.IRSProfile.encoder (message T) ∈ (Benchmark.IRSProfile.code : Set _) := by
  rw [← Benchmark.IRSProfile.encoder_range]
  exact Set.mem_range_self (message T)

theorem fold_close (T : ChosenSets) (δ : ℝ≥0)
    (hδ : ProximityGap.gridPt (ι := I) unsafeIndex ≤ δ)
    (hupper : δ < ProximityGap.gridPt (ι := I) bridgeIndex) :
    δᵣ(word0 + challenge T.1 • word1,
      (Benchmark.IRSProfile.code : Set (I → Fin s → F))) ≤ δ := by
  have htoCode := Code.relDistFromCode_le_relDist_to_mem
    (word0 + challenge T.1 • word1)
    (Benchmark.IRSProfile.encoder (message T.1)) (encoder_message_mem_code T.1)
  refine htoCode.trans ?_
  have hpair :
      ((Code.relHammingDist (word0 + challenge T.1 • word1)
        (Benchmark.IRSProfile.encoder (message T.1)) : ℚ≥0) : ℝ≥0) ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨agreementIndices T.1, ?_, ?_⟩
    · rw [Code.relDist_floor_bound_iff_complement_bound, agreementIndices_card]
      have hge : (unsafeIndex : ℝ≥0) / 262144 ≤ δ := by
        simpa [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index] using hδ
      have hδle : δ ≤ 1 := by
        exact (hupper.trans (by
          norm_num [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index,
            bridgeIndex])).le
      have hgeR := NNReal.coe_le_coe.mpr hge
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδle]
      norm_num [unsafeIndex, agreement, I, Benchmark.IRSProfile.Index] at hgeR ⊢
      linarith
    · intro j
      refine ⟨fun hj => fold_agrees T j hj, ?_⟩
      intro hne hj
      exact hne (fold_agrees T j hj)
  calc
    (Code.relHammingDist (word0 + challenge T.1 • word1)
        (Benchmark.IRSProfile.encoder (message T.1)) : ENNReal) =
        (((Code.relHammingDist (word0 + challenge T.1 • word1)
          (Benchmark.IRSProfile.encoder (message T.1)) : ℚ≥0) : ℝ≥0) : ENNReal) := by
      norm_cast
    _ ≤ (δ : ENNReal) := by exact_mod_cast hpair

noncomputable def denomPoly : Polynomial F :=
  (Polynomial.X : Polynomial F) ^ fiberSize - Polynomial.C lambda

theorem denomPoly_monic : denomPoly.Monic := by
  exact Polynomial.monic_X_pow_sub_C lambda (by norm_num [fiberSize])

theorem denomPoly_natDegree : denomPoly.natDegree = fiberSize := by
  rw [denomPoly, Polynomial.natDegree_X_pow_sub_C]
  norm_num [fiberSize]

theorem denom_eval_domain_ne_zero (j : I) :
    denomPoly.eval (Benchmark.IRSProfile.domain j) ≠ 0 := by
  have hy := domain_pow_mem_quotientNodesF j
  have hne : Benchmark.IRSProfile.domain j ^ fiberSize ≠ lambda := by
    intro h
    exact lambda_not_mem_quotientNodesF (h ▸ hy)
  simpa [denomPoly] using sub_ne_zero.mpr hne

theorem scalarWord1_eq (j : I) :
    scalarWord1 j = -padPoly.eval (Benchmark.IRSProfile.domain j) /
      denomPoly.eval (Benchmark.IRSProfile.domain j) := by
  have h0 := W0_eval_ne_zero_of_mem_quotientNodesF (domain_pow_mem_quotientNodesF j)
  have hden := denom_eval_domain_ne_zero j
  have hden' : Benchmark.IRSProfile.domain j ^ fiberSize - lambda ≠ 0 := by
    simpa [denomPoly] using hden
  simp only [scalarWord1, W, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, denomPoly, Polynomial.eval_pow]
  field_simp [h0, hden'] <;> ring

lemma card_filter_eval_eq_zero_le_natDegree {Q : Polynomial F} (hQ : Q ≠ 0) :
    (Finset.univ.filter fun j : I => Q.eval (Benchmark.IRSProfile.domain j) = 0).card ≤
      Q.natDegree := by
  classical
  refine le_trans ?_ (le_trans (Multiset.toFinset_card_le Q.roots) (Polynomial.card_roots' Q))
  refine Finset.card_le_card_of_injOn Benchmark.IRSProfile.domain (fun j hj => ?_)
    (fun _ _ _ _ h => Benchmark.IRSProfile.domain.injective h)
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
  exact (Finset.mem_filter.mp hj).2

theorem attackStack_not_joint (δ : ℝ≥0)
    (hδ : δ < ProximityGap.gridPt (ι := I) bridgeIndex) :
    ¬ Code.jointProximity (Benchmark.IRSProfile.code : Set (I → Fin s → F))
      (u := attackStack) δ := by
  rw [← Code.jointAgreement_iff_jointProximity]
  rintro ⟨T, hT, v, hv⟩
  obtain ⟨hv1mem, hv1sub⟩ := hv (1 : Fin 2)
  rw [← Benchmark.IRSProfile.encoder_range] at hv1mem
  obtain ⟨m, hm⟩ := hv1mem
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension m 0)
  have hqdeg : q.degree < (rowK : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension m 0)
    simpa only [rowDimension_eq] using h
  have hqnat : q.natDegree ≤ 131071 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hqnatlt := (Polynomial.natDegree_lt_iff_degree_lt hq0).2 hqdeg
      norm_num [rowK] at hqnatlt ⊢
      omega
  have hTlarge : 131583 < T.card := by
    have hδR : (δ : ℝ) < 122642 / 262144 := by
      have hδcoe := NNReal.coe_lt_coe.mpr hδ
      norm_num [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index,
        bridgeIndex] at hδcoe ⊢
      exact hδcoe
    have hδone : δ ≤ 1 := by
      exact NNReal.coe_le_coe.mp
        (hδR.trans (by norm_num : (122642 : ℝ) / 262144 < 1)).le
    have hTR := NNReal.coe_le_coe.mpr hT
    rw [NNReal.coe_mul, NNReal.coe_sub hδone] at hTR
    norm_num [I, Benchmark.IRSProfile.Index, bridgeIndex] at hδR hTR ⊢
    nlinarith
  let Q : Polynomial F := q * denomPoly + padPoly
  have hQne : Q ≠ 0 := by
    intro hQ
    by_cases hq0 : q = 0
    · simp only [Q, hq0, zero_mul, zero_add] at hQ
      exact padPoly_monic.ne_zero hQ
    · have hQ' : q * denomPoly + padPoly = 0 := by simpa [Q] using hQ
      have hEq : padPoly = -(q * denomPoly) := by
        linear_combination hQ'
      have hnat := congrArg Polynomial.natDegree hEq
      rw [padPoly_natDegree, Polynomial.natDegree_neg,
        Polynomial.natDegree_mul hq0 denomPoly_monic.ne_zero, denomPoly_natDegree] at hnat
      norm_num [fiberSize] at hnat
  have hQdeg : Q.natDegree ≤ 131583 := by
    calc
      Q.natDegree ≤ max (q * denomPoly).natDegree padPoly.natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 131583 := by
        rw [padPoly_natDegree]
        apply max_le
        · calc
            (q * denomPoly).natDegree ≤ q.natDegree + denomPoly.natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 131071 + 512 := by
              rw [denomPoly_natDegree]
              exact Nat.add_le_add_right hqnat 512
            _ = 131583 := by norm_num
        · norm_num
  have hzero : T ⊆ Finset.univ.filter fun j : I => Q.eval (Benchmark.IRSProfile.domain j) = 0 := by
    intro j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    have hjfilter := Finset.subset_iff.mp hv1sub hj
    rw [Finset.mem_filter] at hjfilter
    have hsym : v 1 j = attackStack 1 j := hjfilter.2
    have hrow := congrFun hsym (0 : Fin s)
    rw [← hm, Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at hrow
    have hqeval : q.eval (Benchmark.IRSProfile.domain j) = scalarWord1 j := by
      simpa [q, attackStack, word1] using hrow
    rw [Q, Polynomial.eval_add, Polynomial.eval_mul, hqeval, scalarWord1_eq]
    field_simp [denom_eval_domain_ne_zero] <;> ring
  have hcard : T.card ≤ Q.natDegree := by
    exact (Finset.card_le_card hzero).trans (card_filter_eval_eq_zero_le_natDegree hQne)
  omega

noncomputable def goodChallenges : Finset F := chosenSets.image challenge

theorem goodChallenges_card : goodChallenges.card = familySize := by
  have hinj : Set.InjOn challenge chosenSets := by
    intro A hA B hB hAB
    let A' : ChosenSets := ⟨A, hA⟩
    let B' : ChosenSets := ⟨B, hB⟩
    have hAB' : challenge A'.1 = challenge B'.1 := hAB
    exact congrArg Subtype.val (challenge_injective hAB')
  rw [goodChallenges, Finset.card_image_of_injOn hinj, chosenSets_card]

theorem family_div_field_le_epsCa (δ : ℝ≥0)
    (hlower : ProximityGap.gridPt (ι := I) unsafeIndex ≤ δ)
    (hupper : δ < ProximityGap.gridPt (ι := I) bridgeIndex) :
    (familySize : ENNReal) / (Fintype.card F : ENNReal) ≤
      ProximityGap.epsCa (F := F) (A := Fin s → F)
        (Benchmark.IRSProfile.code : Set (I → Fin s → F)) δ δ := by
  classical
  rw [ProximityGap.epsCa]
  refine le_iSup_of_le attackStack ?_
  rw [if_neg (attackStack_not_joint δ hupper)]
  have hsubset : goodChallenges ⊆ Finset.univ.filter fun γ : F =>
      δᵣ(attackStack 0 + γ • attackStack 1,
        (Benchmark.IRSProfile.code : Set (I → Fin s → F))) ≤ (δ : ℝ≥0) := by
    intro γ hγ
    rw [goodChallenges, Finset.mem_image] at hγ
    obtain ⟨T, hT, hTγ⟩ := hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hTγ]
    simpa only [attackStack, Fin.cases_zero, Fin.cases_succ] using
      fold_close (⟨T, hT⟩ : ChosenSets) δ hlower hupper
  rw [Probability.prob_uniform_eq_card_filter_div_card
    (P := fun γ : F => δᵣ(attackStack 0 + γ • attackStack 1,
      (Benchmark.IRSProfile.code : Set (I → Fin s → F))) ≤ (δ : ℝ≥0))]
  rw [show ((Fintype.card F : ℝ≥0) : ENNReal) = (Fintype.card F : ENNReal) by
      rw [ENNReal.coe_natCast],
    show (((Finset.univ.filter (fun γ : F =>
      δᵣ(attackStack 0 + γ • attackStack 1,
        (Benchmark.IRSProfile.code : Set (I → Fin s → F))) ≤ (δ : ℝ≥0))).card : ℝ≥0) :
        ENNReal) = ((Finset.univ.filter (fun γ : F =>
      δᵣ(attackStack 0 + γ • attackStack 1,
        (Benchmark.IRSProfile.code : Set (I → Fin s → F))) ≤ (δ : ℝ≥0))).card :
        ENNReal) by rw [ENNReal.coe_natCast]]
  rw [← goodChallenges_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast Finset.card_le_card hsubset

theorem epsilonStar_lt_family_div_field :
    ((ProximityPrize.Benchmark.Upper.epsilonStar : ℝ≥0) : ENNReal) <
      (familySize : ENNReal) / (Fintype.card F : ENNReal) := by
  have hcardF : Fintype.card F = _root_.KoalaBear.fieldSize ^ 6 :=
    _root_.KoalaBear.card_ext6
  have hnn : (ProximityGap.prizeThreshold : ℝ≥0) <
      (familySize : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rw [hcardF]
    unfold ProximityGap.prizeThreshold
    norm_num [familySize, _root_.KoalaBear.fieldSize, div_pow, div_lt_div_iff₀]
  rw [ProximityPrize.Benchmark.Upper.epsilonStar]
  exact_mod_cast hnn

theorem winningSetDensity_gt_epsilonStar (δ : ℝ≥0)
    (hlower : ProximityGap.gridPt (ι := I) unsafeIndex ≤ δ)
    (hupper : δ < ProximityGap.gridPt (ι := I) bridgeIndex) :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      winningSetDensity Benchmark.IRSProfile.encoder δ := by
  have hδpos : (0 : ℝ≥0) < δ := lt_of_lt_of_le (by
    norm_num [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index, unsafeIndex]) hlower
  have hδlt : δ < 1 := hupper.trans (by
    norm_num [ProximityGap.gridPt, I, Benchmark.IRSProfile.Index, bridgeIndex])
  have hca := family_div_field_le_epsCa δ hlower hupper
  have hbridge := ToyProblem.epsCa_le_winningSetDensity
    (C := (Benchmark.IRSProfile.code : Set (I → Fin s → F))) δ hδpos hδlt
    Benchmark.IRSProfile.encoder Benchmark.IRSProfile.encoder_injective
    Benchmark.IRSProfile.encoder_range
  have h := epsilonStar_lt_family_div_field.trans_le (hca.trans hbridge)
  exact_mod_cast h

end IRSProfile
end ProximityPrize.SubmissionUpper.MultiAnchor
