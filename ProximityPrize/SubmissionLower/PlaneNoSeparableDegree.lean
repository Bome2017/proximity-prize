/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneResultantPointCount
import ProximityPrize.SubmissionLower.PlaneResultantIrreducible
import ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
import ProximityPrize.SubmissionLower.LocalMathlib_LinearAlgebra_PrimeCorankDet

/-!
# The planar bidegree bound for the FULL field degree, with no separability

`PlaneFunctionFieldDegree.finrank_le_planar_bound` counts `K`-embeddings of
the coordinate field into an algebraic closure and identifies that count with
`finrank` — which is only legitimate when the extension is separable.  That
identification is the sole reason the contact chain carries strict
characteristic-degree gates.

This module proves the same bidegree bound for `finrank` itself, by replacing
the geometric point count with the algebraic multiplicity of the resultant.
Write `L = K⟮y⟯`, `f = minpoly K y`, `g = minpoly L r`, `m = deg f`,
`n = deg g`.  Then

* the specialised pair `P(y, ·)`, `Q(y, ·)` in `L[Y]` has the common factor
  `g`, so its Sylvester matrix loses at least `n` in rank
  (`sylvester_rank_le_of_common_divisor`);
* a corank of `n` at the prime `f` forces `f ^ n ∣ Res(P, Q)`
  (`LocalMathlibPrimeCorankDet.pow_corank_dvd_det_of_surjective`);
* hence `finrank K E = m * n ≤ deg Res(P, Q)`, which is the bidegree bound.

Inseparability makes the field degree exceed the number of geometric points;
counting resultant multiplicity instead of points is exactly what closes that
gap.  Nothing here assumes `Algebra.IsSeparable` or bounds any degree by the
characteristic.

Not a `ProtocolClaim`, alignment bound, or submission.
-/

namespace ProximityPrize.SubmissionLower.PlaneNoSeparableDegree

open scoped BigOperators

noncomputable section

section Sylvester

variable {L : Type} [Field L] [DecidableEq L]

/-- A common divisor of degree `d` costs the fixed-degree Sylvester matrix
`d` in rank: every element of its image is a multiple of that divisor. -/
theorem sylvester_rank_le_of_common_divisor
    (p q h : Polynomial L) (m n : ℕ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (hne : h ≠ 0) (hdp : h ∣ p) (hdq : h ∣ q) (hle : h.natDegree ≤ m + n) :
    (Polynomial.sylvester p q m n).rank ≤ m + n - h.natDegree := by
  classical
  haveI : FiniteDimensional L (Polynomial.degreeLT L (m + n)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis L (m + n))
  haveI : FiniteDimensional L (Polynomial.degreeLT L (m + n - h.natDegree)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis L (m + n - h.natDegree))
  have hmem : ∀ u : Polynomial.degreeLT L (m + n - h.natDegree),
      h * (u : Polynomial L) ∈ Polynomial.degreeLT L (m + n) := by
    intro u
    rcases eq_or_ne (u : Polynomial L) 0 with hu | hu
    · rw [hu, mul_zero]
      exact Submodule.zero_mem _
    · have hud : (u : Polynomial L).natDegree < m + n - h.natDegree :=
        (Polynomial.natDegree_lt_iff_degree_lt hu).mpr
          (Polynomial.mem_degreeLT.mp u.2)
      have hmul : (h * (u : Polynomial L)).natDegree
          = h.natDegree + (u : Polynomial L).natDegree :=
        Polynomial.natDegree_mul hne hu
      have hlt : (h * (u : Polynomial L)).natDegree < m + n := by omega
      exact Polynomial.mem_degreeLT.mpr
        ((Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero hne hu)).mp hlt)
  let mulH : Polynomial.degreeLT L (m + n - h.natDegree) →ₗ[L]
      Polynomial.degreeLT L (m + n) := {
    toFun := fun u => ⟨h * (u : Polynomial L), hmem u⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      show h * ((a : Polynomial L) + (b : Polynomial L))
        = h * (a : Polynomial L) + h * (b : Polynomial L)
      ring
    map_smul' := by
      intro c a
      apply Subtype.ext
      show h * (c • (a : Polynomial L)) = c • (h * (a : Polynomial L))
      rw [mul_smul_comm] }
  have hrange : LinearMap.range (Polynomial.sylvesterMap p q hp hq) ≤
      LinearMap.range mulH := by
    rintro z ⟨ab, rfl⟩
    have hz : ((Polynomial.sylvesterMap p q hp hq ab : Polynomial.degreeLT L (m + n))
        : Polynomial L) = p * (ab.2 : Polynomial L) + q * (ab.1 : Polynomial L) := rfl
    obtain ⟨c, hc⟩ : h ∣ p * (ab.2 : Polynomial L) + q * (ab.1 : Polynomial L) :=
      dvd_add (Dvd.dvd.mul_right hdp _) (Dvd.dvd.mul_right hdq _)
    have hzmem : h * c ∈ Polynomial.degreeLT L (m + n) := by
      rw [← hc, ← hz]
      exact (Polynomial.sylvesterMap p q hp hq ab).2
    have hcmem : c ∈ Polynomial.degreeLT L (m + n - h.natDegree) := by
      rcases eq_or_ne c 0 with hc0 | hc0
      · rw [hc0]
        exact Submodule.zero_mem _
      · have hlt : (h * c).natDegree < m + n :=
          (Polynomial.natDegree_lt_iff_degree_lt (mul_ne_zero hne hc0)).mpr
            (Polynomial.mem_degreeLT.mp hzmem)
        have hmul : (h * c).natDegree = h.natDegree + c.natDegree :=
          Polynomial.natDegree_mul hne hc0
        have : c.natDegree < m + n - h.natDegree := by omega
        exact Polynomial.mem_degreeLT.mpr
          ((Polynomial.natDegree_lt_iff_degree_lt hc0).mp this)
    refine ⟨⟨c, hcmem⟩, ?_⟩
    apply Subtype.ext
    show h * c = _
    rw [hz, hc]
  calc (Polynomial.sylvester p q m n).rank
      = Module.finrank L (LinearMap.range (Polynomial.sylvesterMap p q hp hq)) :=
        PlaneResultantPointCount.sylvester_rank_eq_finrank_range p q m n hp hq
    _ ≤ Module.finrank L (LinearMap.range mulH) := Submodule.finrank_mono hrange
    _ ≤ Module.finrank L (Polynomial.degreeLT L (m + n - h.natDegree)) :=
        LinearMap.finrank_range_le mulH
    _ = m + n - h.natDegree := PlaneResultantPointCount.finrank_degreeLT _

end Sylvester

section Assembly

variable (K E : Type) [Field K] [Field E] [Algebra K E]

open PlaneFunctionFieldDegree

/-- The two plane equations force the resultant to vanish at the first
coordinate.  No degree, characteristic, or separability hypothesis. -/
theorem aeval_resultant_eq_zero
    (P Q : Polynomial (Polynomial K)) (hdeg : 0 < P.natDegree) (y r : E)
    (hPy : planeEval K E y r P = 0) (hQy : planeEval K E y r Q = 0) :
    Polynomial.eval₂ (algebraMap K E) y
      (Polynomial.resultant P Q P.natDegree Q.natDegree) = 0 := by
  classical
  set ψ : Polynomial K →+* E := Polynomial.eval₂RingHom (algebraMap K E) y with hψ
  have hPmap : (P.map ψ).eval r = 0 := hPy
  have hQmap : (Q.map ψ).eval r = 0 := hQy
  have hPdeg : (P.map ψ).natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
  have hQdeg : (Q.map ψ).natDegree ≤ Q.natDegree := Polynomial.natDegree_map_le
  obtain ⟨a, b, -, -, hab⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant (P.map ψ) (Q.map ψ) hPdeg hQdeg
      (Or.inl (Nat.ne_of_gt hdeg))
  have heval := congrArg (Polynomial.eval r) hab
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hPmap, hQmap,
    zero_mul, zero_mul, add_zero, Polynomial.eval_C] at heval
  have hmap : Polynomial.resultant (P.map ψ) (Q.map ψ) P.natDegree Q.natDegree
      = ψ (Polynomial.resultant P Q P.natDegree Q.natDegree) :=
    Polynomial.resultant_map_map (f := P) (g := Q)
      (m := P.natDegree) (n := Q.natDegree) ψ
  rw [hmap] at heval
  exact heval.symm

/-- **The planar bidegree bound for the full field degree.**

Only the original irreducibility and properness gates are used.  The proof
counts resultant multiplicity at the minimal polynomial of `y`, so it is
insensitive to inseparability of `E / K`. -/
theorem finite_and_finrank_le_planar_bound
    (P Q : Polynomial (Polynomial K))
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) (hproper : ¬ P ∣ Q)
    (y r : E) (hgen : IntermediateField.adjoin K ({y, r} : Set E) = ⊤)
    (hPy : planeEval K E y r P = 0) (hQy : planeEval K E y r Q = 0) :
    FiniteDimensional K E ∧
      Module.finrank K E ≤ Q.natDegree * Polynomial.Bivariate.degreeX P +
        P.natDegree * Polynomial.Bivariate.degreeX Q := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq E := Classical.decEq E
  set d : ℕ := P.natDegree with hd
  set e : ℕ := Q.natDegree with he
  set R : Polynomial K := Polynomial.resultant P Q d e with hR
  have hRne : R ≠ 0 :=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd P Q hP hdeg hproper
  -- the first coordinate is a root of the nonzero resultant, hence integral
  have hRy : Polynomial.aeval y R = 0 := by
    rw [Polynomial.aeval_def]
    exact aeval_resultant_eq_zero K E P Q hdeg y r hPy hQy
  have hyint : IsIntegral K y :=
    (IsAlgebraic.isIntegral ⟨R, hRne, hRy⟩)
  set f : Polynomial K := minpoly K y with hf
  have hfirr : Irreducible f := minpoly.irreducible hyint
  have hfprime : Prime f := hfirr.prime
  -- the simple extension generated by the first coordinate
  set L : IntermediateField K E := IntermediateField.adjoin K ({y} : Set E) with hL
  set gen : L := IntermediateField.AdjoinSimple.gen K y with hgenL
  have hgenmap : algebraMap L E gen = y := IntermediateField.AdjoinSimple.algebraMap_gen K y
  have hgenint : IsIntegral K gen :=
    (IntermediateField.AdjoinSimple.isIntegral_gen K y).mpr hyint
  set pb : PowerBasis K L := IntermediateField.adjoin.powerBasis hyint with hpb
  have hpbgen : pb.gen = gen := rfl
  haveI : FiniteDimensional K L := pb.finite
  have hfinrankL : Module.finrank K L = f.natDegree :=
    IntermediateField.adjoin.finrank hyint
  -- the residue map
  set φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) gen with hφ
  have hφaeval : ∀ p : Polynomial K, φ p = Polynomial.aeval gen p := fun p => rfl
  have hφsurj : Function.Surjective φ := by
    intro z
    obtain ⟨p, hp⟩ := pb.exists_eq_aeval' z
    exact ⟨p, by rw [hφaeval, ← hpbgen, ← hp]⟩
  have hgenminpoly : minpoly K gen = f := by
    rw [hf, hgenL]
    exact IntermediateField.minpoly_gen K y
  have hφker : ∀ p : Polynomial K, φ p = 0 ↔ f ∣ p := by
    intro p
    rw [hφaeval, ← hgenminpoly]
    exact (minpoly.dvd_iff (A := K) (x := gen) (p := p)).symm
  -- transport along the tower
  have hψ : (algebraMap L E).comp φ = Polynomial.eval₂RingHom (algebraMap K E) y := by
    ext p
    · show algebraMap L E (Polynomial.eval₂ (algebraMap K L) gen (Polynomial.C p))
        = Polynomial.eval₂ (algebraMap K E) y (Polynomial.C p)
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C,
        ← IsScalarTower.algebraMap_apply K L E]
    · show algebraMap L E (Polynomial.eval₂ (algebraMap K L) gen Polynomial.X)
        = Polynomial.eval₂ (algebraMap K E) y Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hgenmap]
  have htransport : ∀ T : Polynomial (Polynomial K),
      (T.map φ).map (algebraMap L E) = T.map (Polynomial.eval₂RingHom (algebraMap K E) y) := by
    intro T
    rw [Polynomial.map_map, hψ]
  -- the specialised pair over `L`
  set PL : Polynomial L := P.map φ with hPL
  set QL : Polynomial L := Q.map φ with hQL
  have hPLne : PL ≠ 0 := by
    intro hzero
    have hcoeff : ∀ i, f ∣ P.coeff i := by
      intro i
      refine (hφker _).mp ?_
      have := congrArg (fun T : Polynomial L => T.coeff i) hzero
      simpa [hPL, Polynomial.coeff_map] using this
    have hdvd : Polynomial.C f ∣ P := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      exact hcoeff
    exact hfirr.not_isUnit (hP.isPrimitive (Nat.ne_of_gt hdeg) f hdvd)
  have hPLroot : Polynomial.aeval r PL = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, htransport]
    exact hPy
  have hQLroot : Polynomial.aeval r QL = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, htransport]
    exact hQy
  -- the second coordinate over the simple extension
  have hrint : IsIntegral L r := IsAlgebraic.isIntegral ⟨PL, hPLne, hPLroot⟩
  set g : Polynomial L := minpoly L r with hg
  set nn : ℕ := g.natDegree with hnn
  have hgdvdP : g ∣ PL := minpoly.dvd L r hPLroot
  have hgdvdQ : g ∣ QL := minpoly.dvd L r hQLroot
  have hgne : g ≠ 0 := minpoly.ne_zero hrint
  have hPLdeg : PL.natDegree ≤ d := Polynomial.natDegree_map_le
  have hQLdeg : QL.natDegree ≤ e := Polynomial.natDegree_map_le
  have hnnle : nn ≤ d :=
    le_trans (Polynomial.natDegree_le_of_dvd hgdvdP hPLne) hPLdeg
  -- corank at the prime `f`
  have hrank : (Polynomial.sylvester PL QL d e).rank ≤ d + e - nn :=
    sylvester_rank_le_of_common_divisor PL QL g d e hPLdeg hQLdeg hgne
      hgdvdP hgdvdQ (by omega)
  have hmapsyl : (Polynomial.sylvester P Q d e).map φ
      = Polynomial.sylvester PL QL d e := by
    rw [hPL, hQL, Polynomial.sylvester_map_map]
    rfl
  have hcorank :=
    LocalMathlibPrimeCorankDet.pow_corank_dvd_det_of_surjective φ hφsurj f hfprime
      hφker (Polynomial.sylvester P Q d e)
  rw [hmapsyl, Fintype.card_fin] at hcorank
  have hdet : (Polynomial.sylvester P Q d e).det = R := rfl
  rw [hdet] at hcorank
  have hpowdvd : f ^ nn ∣ R :=
    dvd_trans (pow_dvd_pow f (by omega)) hcorank
  -- the degree ledger
  have hdegprod : f.natDegree * nn ≤ R.natDegree := by
    have hle := Polynomial.natDegree_le_of_dvd hpowdvd hRne
    rw [Polynomial.natDegree_pow, mul_comm] at hle
    exact hle
  -- the tower degree is exactly that product
  have htop : IntermediateField.adjoin L ({r} : Set E) = ⊤ := by
    refine eq_top_iff.mpr (fun z _ => ?_)
    have hsub : IntermediateField.adjoin K ({y, r} : Set E) ≤
        (IntermediateField.adjoin L ({r} : Set E)).restrictScalars K := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro w hw
      rcases hw with hw | hw
      · subst hw
        show w ∈ IntermediateField.adjoin L ({r} : Set E)
        have : algebraMap L E gen ∈ IntermediateField.adjoin L ({r} : Set E) :=
          IntermediateField.algebraMap_mem _ gen
        rwa [hgenmap] at this
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact IntermediateField.mem_adjoin_simple_self L w
    have hz : z ∈ IntermediateField.adjoin K ({y, r} : Set E) := by
      rw [hgen]; trivial
    exact hsub hz
  haveI : FiniteDimensional L E := by
    have hfin : FiniteDimensional L (IntermediateField.adjoin L ({r} : Set E)) :=
      IntermediateField.adjoin.finiteDimensional hrint
    rw [htop] at hfin
    exact (IntermediateField.topEquiv (F := L) (E := E)).toLinearEquiv.finiteDimensional
  have hfinrankE : Module.finrank L E = nn := by
    have h1 : Module.finrank L (IntermediateField.adjoin L ({r} : Set E)) = nn :=
      IntermediateField.adjoin.finrank hrint
    rw [htop, IntermediateField.finrank_top'] at h1
    exact h1
  haveI : FiniteDimensional K E := FiniteDimensional.trans K L E
  refine ⟨inferInstance, ?_⟩
  have htower : Module.finrank K L * Module.finrank L E = Module.finrank K E :=
    Module.finrank_mul_finrank K L E
  have hbound : R.natDegree ≤ e * Polynomial.Bivariate.degreeX P +
      d * Polynomial.Bivariate.degreeX Q := by
    rw [hR]
    exact bivariate_resultant_natDegree_le (F := K) P Q d e
  rw [← htower, hfinrankL, hfinrankE]
  exact le_trans hdegprod hbound

end Assembly

end

end ProximityPrize.SubmissionLower.PlaneNoSeparableDegree

#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableDegree.sylvester_rank_le_of_common_divisor
#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableDegree.aeval_resultant_eq_zero
#print axioms
  ProximityPrize.SubmissionLower.PlaneNoSeparableDegree.finite_and_finrank_le_planar_bound
