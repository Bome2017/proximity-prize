/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneNoSeparableMultiplicity

/-!
# One planar budget for a whole family, with no separability

`PlaneFunctionFieldDegree.sum_finrank_le_planar_bound` puts the SUM of all
component degrees in one planar budget by counting embeddings of every
component into a common algebraic closure — again identifying the embedding
count with `finrank`, which needs separability.

Here the same shared budget is obtained from resultant multiplicity.  Group
the components by the minimal polynomial `f` of their first coordinate.
Inside one such fibre every component contributes a distinct monic
irreducible factor `minpoly (AdjoinRoot f) (r i)` of both specialised
polynomials, and distinct monic irreducibles are coprime, so the fibre's
degrees add inside the multiplicity of `f` in the resultant.  Multiplicities
at distinct primes then multiply.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.PlaneNoSeparableFamily

open scoped BigOperators
open PlaneFunctionFieldDegree

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

variable (K : Type) [Field K] {I : Type} [Fintype I] (E : I → Type)
  [∀ i, Field (E i)] [∀ i, Algebra K (E i)]

/-- Every component of one fibre contributes its own degree to the
multiplicity of `f` in the resultant. -/
theorem pow_dvd_resultant_of_fiber
    (P Q : Polynomial (Polynomial K))
    (hP : Irreducible P) (hdeg : 0 < P.natDegree)
    (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i, r i} : Set (E i)) = ⊤)
    (hkernels : Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
    (hPy : ∀ i, planeEval K (E i) (y i) (r i) P = 0)
    (hQy : ∀ i, planeEval K (E i) (y i) (r i) Q = 0)
    (nn : I → ℕ)
    (hnn : ∀ i, Module.finrank K (E i) = (minpoly K (y i)).natDegree * nn i)
    (f : Polynomial K) (hfirr : Irreducible f)
    (J : Finset I) (hJ : ∀ i ∈ J, minpoly K (y i) = f) :
    f ^ (∑ i ∈ J, nn i) ∣
      Polynomial.resultant P Q P.natDegree Q.natDegree := by
  classical
  haveI : Fact (Irreducible f) := ⟨hfirr⟩
  have hfne : f ≠ 0 := hfirr.ne_zero
  have hfdeg : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · exact absurd (Polynomial.isUnit_iff_degree_eq_zero.mpr
        (Polynomial.degree_eq_zero_of_isUnit
          (by
            have : f.degree = 0 := by
              rcases Polynomial.natDegree_eq_zero.mp h with ⟨c, rfl⟩
              have hc : c ≠ 0 := by
                intro hc; exact hfne (by rw [hc, map_zero])
              simpa using Polynomial.degree_C hc
            exact Polynomial.isUnit_iff_degree_eq_zero.mpr this))) hfirr.not_isUnit
    · exact h
  -- the residue field does not annihilate the curve
  have hPmapne : P.map (AdjoinRoot.mk f) ≠ 0 := by
    intro hzero
    have hcoeff : ∀ k, f ∣ P.coeff k := by
      intro k
      refine AdjoinRoot.mk_eq_zero.mp ?_
      have hk := congrArg (fun T : Polynomial (AdjoinRoot f) => T.coeff k) hzero
      simpa [Polynomial.coeff_map] using hk
    have hdvd : Polynomial.C f ∣ P := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      exact hcoeff
    exact hfirr.not_isUnit (hP.isPrimitive (Nat.ne_of_gt hdeg) f hdvd)
  -- index the fibre
  have hroot : ∀ j : {i // i ∈ J},
      Polynomial.eval₂ (algebraMap K (E j.1)) (y j.1) f = 0 := by
    intro j
    rw [← Polynomial.aeval_def, ← hJ j.1 j.2]
    exact minpoly.aeval K (y j.1)
  letI alg : ∀ j : {i // i ∈ J}, Algebra (AdjoinRoot f) (E j.1) := fun j =>
    (AdjoinRoot.lift (algebraMap K (E j.1)) (y j.1) (hroot j)).toAlgebra
  have halgmap : ∀ j : {i // i ∈ J},
      (algebraMap (AdjoinRoot f) (E j.1) : AdjoinRoot f →+* E j.1)
        = AdjoinRoot.lift (algebraMap K (E j.1)) (y j.1) (hroot j) := fun _ => rfl
  haveI tower : ∀ j : {i // i ∈ J}, IsScalarTower K (AdjoinRoot f) (E j.1) := by
    intro j
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [halgmap j, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have hrooteq : ∀ j : {i // i ∈ J},
      algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f) = y j.1 := by
    intro j
    rw [halgmap j, AdjoinRoot.lift_root]
  have hcomp : ∀ j : {i // i ∈ J},
      (algebraMap (AdjoinRoot f) (E j.1)).comp (AdjoinRoot.mk f)
        = Polynomial.eval₂RingHom (algebraMap K (E j.1)) (y j.1) := by
    intro j
    ext p
    · show algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.mk f (Polynomial.C p))
        = Polynomial.eval₂ (algebraMap K (E j.1)) (y j.1) (Polynomial.C p)
      rw [Polynomial.eval₂_C, AdjoinRoot.mk_C, halgmap j, AdjoinRoot.lift_of]
    · show algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.mk f Polynomial.X)
        = Polynomial.eval₂ (algebraMap K (E j.1)) (y j.1) Polynomial.X
      rw [Polynomial.eval₂_X]
      exact hrooteq j
  have hnat : ∀ (j : {i // i ∈ J}) (T : Polynomial (Polynomial K)),
      Polynomial.aeval (r j.1) (T.map (AdjoinRoot.mk f))
        = planeEval K (E j.1) (y j.1) (r j.1) T := by
    intro j T
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map, hcomp j]
    rfl
  -- the minimal polynomial of the second coordinate over the residue field
  have hrint : ∀ j : {i // i ∈ J}, IsIntegral (AdjoinRoot f) (r j.1) := by
    intro j
    refine IsAlgebraic.isIntegral ⟨P.map (AdjoinRoot.mk f), hPmapne, ?_⟩
    rw [hnat j P]
    exact hPy j.1
  set G : {i // i ∈ J} → Polynomial (AdjoinRoot f) :=
    fun j => minpoly (AdjoinRoot f) (r j.1) with hG
  have hGmonic : ∀ j, (G j).Monic := fun j => minpoly.monic (hrint j)
  have hGirr : ∀ j, Irreducible (G j) := fun j => minpoly.irreducible (hrint j)
  have hGdvd : ∀ (j : {i // i ∈ J}) (T : Polynomial (Polynomial K)),
      G j ∣ T.map (AdjoinRoot.mk f) ↔ planeEval K (E j.1) (y j.1) (r j.1) T = 0 := by
    intro j T
    rw [← hnat j T]
    exact minpoly.dvd_iff
  have hGdvdP : ∀ j, G j ∣ P.map (AdjoinRoot.mk f) :=
    fun j => (hGdvd j P).mpr (hPy j.1)
  have hGdvdQ : ∀ j, G j ∣ Q.map (AdjoinRoot.mk f) :=
    fun j => (hGdvd j Q).mpr (hQy j.1)
  have hGinj : Function.Injective G := by
    intro j j' hjj
    have hideal : relationIdeal K (E j.1) (y j.1) (r j.1)
        = relationIdeal K (E j'.1) (y j'.1) (r j'.1) := by
      ext T
      show planeEval K (E j.1) (y j.1) (r j.1) T = 0 ↔
        planeEval K (E j'.1) (y j'.1) (r j'.1) T = 0
      rw [← hGdvd j T, ← hGdvd j' T, hjj]
    exact Subtype.ext (hkernels hideal)
  -- the degree of each component splits along the tower
  haveI : FiniteDimensional K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hfne).finite
  have hbasedeg : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hfne)]
    rfl
  have hsplit : ∀ j : {i // i ∈ J},
      Module.finrank K (E j.1) = f.natDegree * (G j).natDegree := by
    intro j
    have htop : IntermediateField.adjoin (AdjoinRoot f) ({r j.1} : Set (E j.1)) = ⊤ := by
      refine eq_top_iff.mpr (fun z _ => ?_)
      have hsub : IntermediateField.adjoin K ({y j.1, r j.1} : Set (E j.1)) ≤
          (IntermediateField.adjoin (AdjoinRoot f)
            ({r j.1} : Set (E j.1))).restrictScalars K := by
        refine IntermediateField.adjoin_le_iff.mpr ?_
        intro w hw
        rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
        rcases hw with hw | hw
        · have hmem : algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f) ∈
              IntermediateField.adjoin (AdjoinRoot f) ({r j.1} : Set (E j.1)) :=
            IntermediateField.algebraMap_mem _ _
          rw [hrooteq j] at hmem
          rw [hw]
          exact hmem
        · rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact IntermediateField.mem_adjoin_simple_self (AdjoinRoot f) (r j.1)
      have hz : z ∈ IntermediateField.adjoin K ({y j.1, r j.1} : Set (E j.1)) := by
        rw [hgen j.1]; trivial
      exact hsub hz
    haveI : FiniteDimensional (AdjoinRoot f) (E j.1) := by
      have hfin : FiniteDimensional (AdjoinRoot f)
          (IntermediateField.adjoin (AdjoinRoot f) ({r j.1} : Set (E j.1))) :=
        IntermediateField.adjoin.finiteDimensional (hrint j)
      rw [htop] at hfin
      exact (IntermediateField.topEquiv (F := AdjoinRoot f)
        (E := E j.1)).toLinearEquiv.finiteDimensional
    have hupper : Module.finrank (AdjoinRoot f) (E j.1) = (G j).natDegree := by
      have h1 : Module.finrank (AdjoinRoot f)
          (IntermediateField.adjoin (AdjoinRoot f) ({r j.1} : Set (E j.1)))
            = (G j).natDegree := IntermediateField.adjoin.finrank (hrint j)
      rw [htop, IntermediateField.finrank_top'] at h1
      exact h1
    rw [← Module.finrank_mul_finrank K (AdjoinRoot f) (E j.1), hbasedeg, hupper]
  -- the fibre degrees are exactly the summands
  have hnneq : ∀ j : {i // i ∈ J}, nn j.1 = (G j).natDegree := by
    intro j
    have h1 := hnn j.1
    rw [hJ j.1 j.2, hsplit j] at h1
    exact Nat.eq_of_mul_eq_mul_left hfdeg h1.symm
  have hsum : (∑ i ∈ J, nn i) = ∑ j : {i // i ∈ J}, (G j).natDegree := by
    rw [← Finset.sum_coe_sort J nn]
    exact Finset.sum_congr rfl (fun j _ => hnneq j)
  rw [hsum]
  exact PlaneNoSeparableMultiplicity.pow_sum_dvd_resultant P Q f G
    hGmonic hGirr hGinj hGdvdP hGdvdQ hPmapne

/-- **One planar bidegree budget for the whole family, with no
separability.** -/
theorem sum_finrank_le_planar_bound
    (P Q : Polynomial (Polynomial K))
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) (hproper : ¬ P ∣ Q)
    (y r : ∀ i, E i)
    (hgen : ∀ i, IntermediateField.adjoin K ({y i, r i} : Set (E i)) = ⊤)
    (hkernels : Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
    (hPy : ∀ i, planeEval K (E i) (y i) (r i) P = 0)
    (hQy : ∀ i, planeEval K (E i) (y i) (r i) Q = 0) :
    (∑ i, Module.finrank K (E i)) ≤
      Q.natDegree * Polynomial.Bivariate.degreeX P +
        P.natDegree * Polynomial.Bivariate.degreeX Q := by
  classical
  letI : DecidableEq I := Classical.decEq I
  letI : DecidableEq K := Classical.decEq K
  set R := Polynomial.resultant P Q P.natDegree Q.natDegree with hR
  have hRne : R ≠ 0 :=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd P Q hP hdeg hproper
  -- each first coordinate is integral, with its degree dividing the total
  have hyint : ∀ i, IsIntegral K (y i) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨R, hRne, ?_⟩
    rw [Polynomial.aeval_def, hR]
    exact PlaneNoSeparableDegree.aeval_resultant_eq_zero K (E i) P Q hdeg
      (y i) (r i) (hPy i) (hQy i)
  have hdvd : ∀ i, (minpoly K (y i)).natDegree ∣ Module.finrank K (E i) := by
    intro i
    haveI : FiniteDimensional K (E i) :=
      (PlaneNoSeparableDegree.finite_and_finrank_le_planar_bound K (E i) P Q
        hP hdeg hproper (y i) (r i) (hgen i) (hPy i) (hQy i)).1
    have h1 : Module.finrank K (IntermediateField.adjoin K ({y i} : Set (E i)))
        = (minpoly K (y i)).natDegree := IntermediateField.adjoin.finrank (hyint i)
    refine ⟨Module.finrank (IntermediateField.adjoin K ({y i} : Set (E i))) (E i), ?_⟩
    rw [← h1]
    exact (Module.finrank_mul_finrank K
      (IntermediateField.adjoin K ({y i} : Set (E i))) (E i)).symm
  choose nn hnn using hdvd
  -- every prime gets its fibre's worth of multiplicity
  have hper : ∀ f : Polynomial K,
      f ^ (∑ i ∈ Finset.univ.filter (fun i => minpoly K (y i) = f), nn i) ∣ R := by
    intro f
    rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun i => minpoly K (y i) = f)) with hempty | ⟨i₀, hi₀⟩
    · rw [hempty]
      simpa using one_dvd R
    · have hf : minpoly K (y i₀) = f := (Finset.mem_filter.mp hi₀).2
      have hfirr : Irreducible f := hf ▸ minpoly.irreducible (hyint i₀)
      exact pow_dvd_resultant_of_fiber K E P Q hP hdeg y r hgen hkernels hPy hQy
        nn hnn f hfirr _ (fun i hi => (Finset.mem_filter.mp hi).2)
  have hprod : (∏ i, minpoly K (y i) ^ nn i) ∣ R :=
    PlaneNoSeparableMultiplicity.prod_pow_dvd_of_per_prime
      (fun i => minpoly K (y i)) nn R (fun i => minpoly.monic (hyint i))
      (fun i => minpoly.irreducible (hyint i)) Finset.univ hper
  -- and the degrees add up
  have hdegprod : (∑ i, Module.finrank K (E i)) ≤ R.natDegree := by
    have hle := Polynomial.natDegree_le_of_dvd hprod hRne
    have hcalc : (∏ i, minpoly K (y i) ^ nn i).natDegree
        = ∑ i, Module.finrank K (E i) := by
      rw [Polynomial.natDegree_prod _ _
        (fun i _ => pow_ne_zero _ (minpoly.ne_zero (hyint i)))]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Polynomial.natDegree_pow, mul_comm, ← hnn i])
    rwa [hcalc] at hle
  exact le_trans hdegprod
    (by rw [hR]; exact bivariate_resultant_natDegree_le (F := K) P Q P.natDegree Q.natDegree)

end

end ProximityPrize.SubmissionLower.PlaneNoSeparableFamily

#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableFamily.pow_dvd_resultant_of_fiber
#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableFamily.sum_finrank_le_planar_bound
