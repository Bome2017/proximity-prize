import ProximityPrize.SubmissionLower.RFreeScaledJetBridge
import ProximityPrize.SubmissionLower.L4

namespace ProximityPrize.SubmissionLower.RFreeBasisOrders

open ContactKernelCommonGCDResearch
open ContactFlagInterpolation6641Research
open RFreeDerivativeTransport

noncomputable section
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

variable (d w L : ℕ)
variable (W : Submodule K (globalCoefficientBox K d w L 0))
local instance : Module.Free K W := Module.Free.of_divisionRing K W

def scaledTranslationAt (x u0 u1 : K) :
    W →ₗ[K] ScaledPolynomial K :=
  (scaledLocalTranslation K x u0 u1).toLinearMap.comp
    ((globalCoefficientBox K d w L 0).subtype.comp W.subtype)

noncomputable local instance basisIndexFintype [Module.Finite K W] :
    Fintype (Module.Free.ChooseBasisIndex K W) :=
  @Fintype.ofFinite _
    (Module.Finite.finite_basis (Module.Free.chooseBasis K W))

def basisScaledPolynomial (x u0 u1 : K)
    (j : Module.Free.ChooseBasisIndex K W) :
    ScaledPolynomial K :=
  scaledTranslationAt d w L W x u0 u1
    (Module.Free.chooseBasis K W j)

def nonzeroBasisOrders [Module.Finite K W] (x u0 u1 : K) : Finset ℕ := by
  classical
  exact (Finset.univ.filter fun j : Module.Free.ChooseBasisIndex K W ↦
    basisScaledPolynomial d w L W x u0 u1 j ≠ 0).image
      (fun j ↦ (basisScaledPolynomial d w L W x u0 u1 j).natTrailingDegree)

def cappedLocalOrder [Module.Finite K W] (x u0 u1 : K) : ℕ :=
  if hs : (nonzeroBasisOrders d w L W x u0 u1).Nonempty then
    min 42 ((nonzeroBasisOrders d w L W x u0 u1).min' hs)
  else 42

theorem cappedLocalOrder_le [Module.Finite K W] (x u0 u1 : K) :
    cappedLocalOrder d w L W x u0 u1 ≤ 42 := by
  classical
  unfold cappedLocalOrder
  split_ifs
  · exact Nat.min_le_left _ _
  · exact le_rfl

theorem basisScaledPolynomial_dvd [Module.Finite K W]
    (x u0 u1 : K) (j : Module.Free.ChooseBasisIndex K W) :
    (Polynomial.X : ScaledPolynomial K) ^
        cappedLocalOrder d w L W x u0 u1 ∣
      basisScaledPolynomial d w L W x u0 u1 j := by
  classical
  let orders := nonzeroBasisOrders d w L W x u0 u1
  by_cases hs : orders.Nonempty
  · by_cases hz : basisScaledPolynomial d w L W x u0 u1 j = 0
    · rw [hz]
      exact dvd_zero _
    · have hj :
          (basisScaledPolynomial d w L W x u0 u1 j).natTrailingDegree ∈
            orders := by
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      have hle : cappedLocalOrder d w L W x u0 u1 ≤
          (basisScaledPolynomial d w L W x u0 u1 j).natTrailingDegree := by
        rw [cappedLocalOrder]
        simp only [show nonzeroBasisOrders d w L W x u0 u1 = orders by rfl,
          dif_pos hs]
        exact (Nat.min_le_right _ _).trans (Finset.min'_le orders _ hj)
      exact X_pow_dvd_of_le_natTrailingDegree K _ _ hle
  · have hz : basisScaledPolynomial d w L W x u0 u1 j = 0 := by
      by_contra hn
      apply hs
      refine ⟨(basisScaledPolynomial d w L W x u0 u1 j).natTrailingDegree, ?_⟩
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    rw [hz]
    exact dvd_zero _

theorem scaledTranslation_dvd [Module.Finite K W]
    (x u0 u1 : K) (Q : W) :
    (Polynomial.X : ScaledPolynomial K) ^
        cappedLocalOrder d w L W x u0 u1 ∣
      scaledTranslationAt d w L W x u0 u1 Q := by
  classical
  let b := Module.Free.chooseBasis K W
  rw [← b.sum_repr Q, map_sum]
  apply Finset.dvd_sum
  intro j hj
  rw [map_smul]
  rw [Algebra.smul_def]
  change _ ∣ (algebraMap K (ScaledPolynomial K) (b.repr Q j)) *
    basisScaledPolynomial d w L W x u0 u1 j
  exact dvd_mul_of_dvd_right
    (basisScaledPolynomial_dvd d w L W x u0 u1 j)
    (algebraMap K (ScaledPolynomial K) (b.repr Q j))

theorem exists_basis_exact_of_cappedLocalOrder_lt
    [Module.Finite K W] (x u0 u1 : K)
    (hlt : cappedLocalOrder d w L W x u0 u1 < 42) :
    ∃ j : Module.Free.ChooseBasisIndex K W,
      HasExactScaledOrder K
        (basisScaledPolynomial d w L W x u0 u1 j)
        (cappedLocalOrder d w L W x u0 u1) := by
  classical
  let orders := nonzeroBasisOrders d w L W x u0 u1
  have hs : orders.Nonempty := by
    by_contra hempty
    have heq : cappedLocalOrder d w L W x u0 u1 = 42 := by
      rw [cappedLocalOrder]
      simp only [show nonzeroBasisOrders d w L W x u0 u1 = orders by rfl,
        dif_neg hempty]
    omega
  have horder : cappedLocalOrder d w L W x u0 u1 = orders.min' hs := by
    have hmin : min 42 (orders.min' hs) < 42 := by
      simpa [cappedLocalOrder,
        show nonzeroBasisOrders d w L W x u0 u1 = orders by rfl, hs] using hlt
    have hle : orders.min' hs ≤ 42 := by
      by_contra hnot
      have hge : 42 ≤ orders.min' hs := Nat.le_of_not_ge hnot
      rw [Nat.min_eq_left hge] at hmin
      exact (Nat.lt_irrefl 42) hmin
    rw [cappedLocalOrder]
    simp only [show nonzeroBasisOrders d w L W x u0 u1 = orders by rfl,
      dif_pos hs, Nat.min_eq_right hle]
  have hmem := Finset.min'_mem orders hs
  dsimp [orders, nonzeroBasisOrders] at hmem
  rcases Finset.mem_image.mp hmem with ⟨j, hj, hdegree⟩
  have hne : basisScaledPolynomial d w L W x u0 u1 j ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  refine ⟨j, hne, ?_⟩
  exact hdegree.trans horder.symm

end
end ProximityPrize.SubmissionLower.RFreeBasisOrders
