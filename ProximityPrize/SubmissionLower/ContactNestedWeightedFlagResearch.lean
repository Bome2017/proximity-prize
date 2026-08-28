import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.TrivariateShearResearch
import ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactGenericSurface

namespace ProximityPrize.SubmissionLower.ContactNestedWeightedFlagResearch

open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactProfileYZFactorLedgerResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactGenericSurface ContactRobustFixedMeet6656Research

noncomputable section

def curveRWeights : Fin 3 → ℕ := fun i ↦ if i = 1 then 1 else 0
def curveYRWeights : Fin 3 → ℕ := fun i ↦ if i = 2 then 0 else 1
def curveTotalWeights : Fin 3 → ℕ := fun _ ↦ 1

def curveWt {K : Type} [Field K] (weights : Fin 3 → ℕ)
    (F : MvPolynomial (Fin 3) K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights F

def curveNestedFlag {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) : FlagDegree :=
  ⟨curveWt curveTotalWeights F - curveWt curveYRWeights F,
    curveWt curveYRWeights F - curveWt curveRWeights F,
    curveWt curveRWeights F⟩

def surfaceNestedFlag {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) : FlagDegree :=
  ⟨MvPolynomial.weightedTotalDegree residualTotalWeights F -
      MvPolynomial.weightedTotalDegree residualYSWeights F,
    MvPolynomial.weightedTotalDegree residualYSWeights F -
      MvPolynomial.weightedTotalDegree residualSWeights F,
    MvPolynomial.weightedTotalDegree residualSWeights F⟩

theorem surfaceWt_s_le_ys {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree residualSWeights F ≤
      MvPolynomial.weightedTotalDegree residualYSWeights F := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [ContactFactorCaps.weight_fin4] at h ⊢
  norm_num [residualSWeights, residualYSWeights] at h ⊢
  exact (Nat.le_add_left _ _).trans h

theorem surfaceWt_ys_le_total {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree residualYSWeights F ≤
      MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [ContactFactorCaps.weight_fin4] at h ⊢
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ _ at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ _
  norm_num at h ⊢
  exact (Nat.le_add_right (d 1 + d 2) (d 3)).trans h

theorem surfaceNestedFlag_all {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) :
    (surfaceNestedFlag F).all =
      MvPolynomial.weightedTotalDegree residualSWeights F := rfl

theorem surfaceNestedFlag_ys {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) :
    (surfaceNestedFlag F).yz + (surfaceNestedFlag F).all =
      MvPolynomial.weightedTotalDegree residualYSWeights F := by
  exact Nat.sub_add_cancel (surfaceWt_s_le_ys F)

theorem surfaceNestedFlag_total {K : Type} [Field K]
    (F : MvPolynomial (Fin 4) K) :
    (surfaceNestedFlag F).zOnly + (surfaceNestedFlag F).yz +
        (surfaceNestedFlag F).all =
      MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  rw [Nat.add_assoc, surfaceNestedFlag_ys]
  exact Nat.sub_add_cancel (surfaceWt_ys_le_total F)

theorem curveWt_r_le_yr {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    curveWt curveRWeights F ≤ curveWt curveYRWeights F := by
  unfold curveWt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree curveYRWeights hd
  rw [TrivariateShearResearch.weight_fin3] at h ⊢
  norm_num [curveRWeights, curveYRWeights] at h ⊢
  exact (Nat.le_add_left _ _).trans h

theorem curveWt_yr_le_total {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    curveWt curveYRWeights F ≤ curveWt curveTotalWeights F := by
  unfold curveWt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree curveTotalWeights hd
  rw [TrivariateShearResearch.weight_fin3] at h ⊢
  norm_num [curveYRWeights, curveTotalWeights] at h ⊢
  exact (Nat.le_add_right (d 0 + d 1) (d 2)).trans h

theorem curveNestedFlag_all {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).all = curveWt curveRWeights F := rfl

theorem curveNestedFlag_yr {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).yz + (curveNestedFlag F).all =
      curveWt curveYRWeights F := by
  simp only [curveNestedFlag, curveNestedFlag_all]
  exact Nat.sub_add_cancel (curveWt_r_le_yr F)

theorem curveNestedFlag_total {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).zOnly + (curveNestedFlag F).yz +
        (curveNestedFlag F).all = curveWt curveTotalWeights F := by
  rw [Nat.add_assoc, curveNestedFlag_yr]
  exact Nat.sub_add_cancel (curveWt_yr_le_total F)

theorem polynomialIn_curveNestedFlag {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) : PolynomialInFlag (curveNestedFlag F) F := by
  intro d hd
  have hr := MvPolynomial.le_weightedTotalDegree curveRWeights hd
  have hyr := MvPolynomial.le_weightedTotalDegree curveYRWeights hd
  have ht := MvPolynomial.le_weightedTotalDegree curveTotalWeights hd
  rw [TrivariateShearResearch.weight_fin3] at hr hyr ht
  norm_num [curveRWeights, curveYRWeights, curveTotalWeights] at hr hyr ht
  change d 1 ≤ (curveNestedFlag F).all ∧
    d 0 + d 1 ≤ (curveNestedFlag F).yz + (curveNestedFlag F).all ∧
    d 0 + d 1 + d 2 ≤ (curveNestedFlag F).zOnly +
      (curveNestedFlag F).yz + (curveNestedFlag F).all
  refine ⟨?_, ?_, ?_⟩
  · change d 1 ≤ curveWt curveRWeights F
    exact hr
  · change d 0 + d 1 ≤
      (curveNestedFlag F).yz + (curveNestedFlag F).all
    rw [curveNestedFlag_yr]
    exact hyr
  · change d 0 + d 1 + d 2 ≤ (curveNestedFlag F).zOnly +
      (curveNestedFlag F).yz + (curveNestedFlag F).all
    rw [curveNestedFlag_total]
    exact ht

theorem curveWt_r_eq_degree {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    curveWt curveRWeights F = F.degreeOf (1 : Fin 3) := by
  have hw : curveRWeights = Pi.single (1 : Fin 3) 1 := by
    funext i
    fin_cases i <;> simp [curveRWeights]
  rw [curveWt, hw, MvPolynomial.weightedTotalDegree_piSingle]

theorem curveWt_yr_le_degrees {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    curveWt curveYRWeights F ≤ F.degreeOf 0 + F.degreeOf 1 := by
  unfold curveWt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  rw [TrivariateShearResearch.weight_fin3]
  norm_num [curveYRWeights]
  exact Nat.add_le_add
    (MvPolynomial.le_degreeOf_of_mem_support 0 hd)
    (MvPolynomial.le_degreeOf_of_mem_support 1 hd)

theorem curveWt_total_le_yr_add_degree {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    curveWt curveTotalWeights F ≤
      curveWt curveYRWeights F + F.degreeOf 2 := by
  unfold curveWt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  rw [TrivariateShearResearch.weight_fin3]
  norm_num [curveTotalWeights]
  have hyr := MvPolynomial.le_weightedTotalDegree curveYRWeights hd
  rw [TrivariateShearResearch.weight_fin3] at hyr
  norm_num [curveYRWeights] at hyr
  exact Nat.add_le_add hyr (MvPolynomial.le_degreeOf_of_mem_support 2 hd)

theorem curveNestedFlag_all_eq_degree {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).all = F.degreeOf 1 := by
  rw [curveNestedFlag_all, curveWt_r_eq_degree]

theorem curveNestedFlag_yz_le_degree {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).yz ≤ F.degreeOf 0 := by
  have h := curveWt_yr_le_degrees F
  change curveWt curveYRWeights F - curveWt curveRWeights F ≤ F.degreeOf 0
  rw [curveWt_r_eq_degree]
  omega

theorem curveNestedFlag_z_le_degree {K : Type} [Field K]
    (F : MvPolynomial (Fin 3) K) :
    (curveNestedFlag F).zOnly ≤ F.degreeOf 2 := by
  have h := curveWt_total_le_yr_add_degree F
  simp only [curveNestedFlag]
  omega

theorem trivariateWeightedLift_ne_zero {K : Type} [Field K]
    (weights : Fin 3 → ℕ) (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) :
    TrivariateShearResearch.weightedLift weights F ≠ 0 := by
  intro h
  apply hF
  apply TrivariateShearResearch.weightedLift_injective weights
  simpa only [map_zero] using h

theorem curveWt_mul {K : Type} [Field K] (weights : Fin 3 → ℕ)
    (F G : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hG : G ≠ 0) :
    curveWt weights (F * G) = curveWt weights F + curveWt weights G := by
  unfold curveWt
  rw [← TrivariateShearResearch.degree_weightedLift,
    map_mul, MvPolynomial.degreeOf_mul_eq
      (trivariateWeightedLift_ne_zero weights F hF)
      (trivariateWeightedLift_ne_zero weights G hG),
    TrivariateShearResearch.degree_weightedLift,
    TrivariateShearResearch.degree_weightedLift]

theorem sum_curveWt_le_of_prod_dvd {K ι : Type} [Field K]
    (weights : Fin 3 → ℕ) (I : Finset ι)
    (f : ι → MvPolynomial (Fin 3) K) (Q : MvPolynomial (Fin 3) K)
    (hQ : Q ≠ 0) (hdiv : (∏ i ∈ I, f i) ∣ Q) :
    (∑ i ∈ I, curveWt weights (f i)) ≤ curveWt weights Q := by
  classical
  have hprod : (∏ i ∈ I, f i) ≠ 0 := by
    intro hz
    obtain ⟨T, rfl⟩ := hdiv
    exact hQ (by rw [hz, zero_mul])
  have hf : ∀ i ∈ I, f i ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  obtain ⟨T, hT⟩ := hdiv
  have hTne : T ≠ 0 := by
    intro hz
    apply hQ
    rw [hT, hz, mul_zero]
  have hsum : curveWt weights (∏ i ∈ I, f i) =
      ∑ i ∈ I, curveWt weights (f i) := by
    calc
      curveWt weights (∏ i ∈ I, f i) =
          (TrivariateShearResearch.weightedLift weights
            (∏ i ∈ I, f i)).degreeOf (3 : Fin 4) :=
        (TrivariateShearResearch.degree_weightedLift weights _).symm
      _ = (∏ i ∈ I,
          TrivariateShearResearch.weightedLift weights (f i)).degreeOf
            (3 : Fin 4) := by rw [map_prod]
      _ = ∑ i ∈ I,
          (TrivariateShearResearch.weightedLift weights (f i)).degreeOf
            (3 : Fin 4) :=
        MvPolynomial.degreeOf_prod_eq I _
          (fun i hi ↦ trivariateWeightedLift_ne_zero weights (f i) (hf i hi))
      _ = ∑ i ∈ I, curveWt weights (f i) := by
        simp only [curveWt, TrivariateShearResearch.degree_weightedLift]
  rw [hT, curveWt_mul weights _ T hprod hTne, hsum]
  exact Nat.le_add_right _ _

theorem surfaceMap_curveWt_le {K Omega : Type} [Field K] [Field Omega]
    (phi : Polynomial K →+* Omega) (weights : Fin 3 → ℕ)
    (weights4 : Fin 4 → ℕ)
    (hw : weights4 0 = 0 ∧ weights4 1 = weights 0 ∧
      weights4 2 = weights 1 ∧ weights4 3 = weights 2)
    (F : MvPolynomial (Fin 4) K) :
    curveWt weights (surfaceMap phi F) ≤
      MvPolynomial.weightedTotalDegree weights4 F := by
  unfold curveWt MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F hd)
  have h := MvPolynomial.le_weightedTotalDegree weights4 hq
  have heq : Finsupp.weight weights q.tail = Finsupp.weight weights4 q := by
    rw [TrivariateShearResearch.weight_fin3,
      ContactFactorCaps.weight_fin4]
    rcases hw with ⟨h0, h1, h2, h3⟩
    simp only [Finsupp.tail_apply,
      show Fin.succ (0 : Fin 3) = (1 : Fin 4) by decide,
      show Fin.succ (1 : Fin 3) = (2 : Fin 4) by decide,
      show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide,
      h0, h1, h2, h3, Nat.mul_zero, Nat.zero_add]
  rw [heq]
  exact h

theorem nested_linear_sum_le {I : Type} [Fintype I]
    (z y a : I → ℕ) (capZ capY capA cz cy ca : ℕ)
    (hcz : cz ≤ cy) (hcy : cy ≤ ca)
    (ha : (∑ i, a i) ≤ capA)
    (hy : (∑ i, (y i + a i)) ≤ capY + capA)
    (hz : (∑ i, (z i + y i + a i)) ≤ capZ + capY + capA) :
    (∑ i, (z i * cz + y i * cy + a i * ca)) ≤
      capZ * cz + capY * cy + capA * ca := by
  let dy := cy - cz
  let da := ca - cy
  have ecy : cy = cz + dy := (Nat.add_sub_of_le hcz).symm
  have eca : ca = cz + dy + da := by
    dsimp only [dy, da]
    omega
  have h0 := Nat.mul_le_mul_right cz hz
  have h1 := Nat.mul_le_mul_right dy hy
  have h2 := Nat.mul_le_mul_right da ha
  calc
    (∑ i, (z i * cz + y i * cy + a i * ca)) =
        ∑ i, ((z i + y i + a i) * cz +
          (y i + a i) * dy + a i * da) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ecy, eca]
      ring
    _ =
        (∑ i, (z i + y i + a i)) * cz +
          (∑ i, (y i + a i)) * dy +
          (∑ i, a i) * da := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ (capZ + capY + capA) * cz + (capY + capA) * dy +
        capA * da := Nat.add_le_add (Nat.add_le_add h0 h1) h2
    _ = capZ * cz + capY * cy + capA * ca := by
      rw [ecy, eca]
      ring

theorem sum_factorRegularLedgerYZForDirection_le_nested
    {I : Type} [Fintype I] (p : Profile) (direction : FlagDegree)
    (flag : I → FlagDegree) (cap : FlagDegree)
    (hzy : factorRegularLedgerYZForDirection p direction unitZFlag ≤
      factorRegularLedgerYZForDirection p direction unitYZFlag)
    (hya : factorRegularLedgerYZForDirection p direction unitYZFlag ≤
      factorRegularLedgerYZForDirection p direction unitAllFlag)
    (hall : (∑ i, (flag i).all) ≤ cap.all)
    (hyr : (∑ i, ((flag i).yz + (flag i).all)) ≤ cap.yz + cap.all)
    (htotal : (∑ i, ((flag i).zOnly + (flag i).yz + (flag i).all)) ≤
      cap.zOnly + cap.yz + cap.all) :
    (∑ i, factorRegularLedgerYZForDirection p direction (flag i)) ≤
      factorRegularLedgerYZForDirection p direction cap := by
  calc
    (∑ i, factorRegularLedgerYZForDirection p direction (flag i)) =
        ∑ i, ((flag i).zOnly *
            factorRegularLedgerYZForDirection p direction unitZFlag +
          (flag i).yz *
            factorRegularLedgerYZForDirection p direction unitYZFlag +
          (flag i).all *
            factorRegularLedgerYZForDirection p direction unitAllFlag) := by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedgerYZForDirection_projection_decomposition
        p direction (flag i)
    _ ≤ cap.zOnly * factorRegularLedgerYZForDirection p direction unitZFlag +
        cap.yz * factorRegularLedgerYZForDirection p direction unitYZFlag +
        cap.all * factorRegularLedgerYZForDirection p direction unitAllFlag :=
      nested_linear_sum_le
        (fun i ↦ (flag i).zOnly) (fun i ↦ (flag i).yz)
        (fun i ↦ (flag i).all) cap.zOnly cap.yz cap.all
        (factorRegularLedgerYZForDirection p direction unitZFlag)
        (factorRegularLedgerYZForDirection p direction unitYZFlag)
        (factorRegularLedgerYZForDirection p direction unitAllFlag)
        hzy hya hall hyr htotal
    _ = factorRegularLedgerYZForDirection p direction cap := by
      exact (factorRegularLedgerYZForDirection_projection_decomposition
        p direction cap).symm

end

end ProximityPrize.SubmissionLower.ContactNestedWeightedFlagResearch
