import ProximityPrize.SubmissionLower.FiniteTaylorQuotientInterpolation
import ProximityPrize.SubmissionLower.FiniteTaylorResultantRigidity
import ProximityPrize.SubmissionLower.AlignmentFromPolynomials
import ProximityPrize.SubmissionLower.AgreementIncidence5314
import ProximityPrize.SubmissionLower.FactorThreshold5314

/-!
# Final alignment assembly from quotient-valued interpolation data

The theorem in this file is deliberately independent of the finite Taylor
construction.  It states exactly what that construction and the resultant
argument must supply, and proves that those data force the selected decoding
polynomials onto one affine line.
-/

namespace ProximityPrize.SubmissionLower.FiniteTaylorAlignmentAssembly

open scoped BigOperators
open Polynomial
open ProximityPrize.Benchmark
open FiniteTaylorCore
open FiniteTaylorQuotientInterpolation
open FiniteTaylorResultantRigidity
open AgreementIncidence5314 FactorThreshold5314

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

/-- Embed an `F[X]` polynomial into `F[Z][T][X]`, preserving the outer
variable and making every coefficient constant in both quotient variables. -/
def liftScalarPolynomial (p : Polynomial IRSProfile.Field) :
    Polynomial (Polynomial (Polynomial IRSProfile.Field)) :=
  p.map ((Polynomial.C : Polynomial IRSProfile.Field →+*
    Polynomial (Polynomial IRSProfile.Field)).comp
      (Polynomial.C : IRSProfile.Field →+* Polynomial IRSProfile.Field))

/-- The universal affine family `p₀(X) + Z p₁(X)` in `F[Z][T][X]`. -/
def liftAffineFamily (p₀ p₁ : Polynomial IRSProfile.Field) :
    Polynomial (Polynomial (Polynomial IRSProfile.Field)) :=
  liftScalarPolynomial p₀ +
    Polynomial.C (Polynomial.C Polynomial.X) * liftScalarPolynomial p₁

/-- Difference between the universal Taylor polynomial and a scaled affine
family. -/
def universalAlignmentDifference
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field)
    (p₀ p₁ : Polynomial IRSProfile.Field) :
    Polynomial (Polynomial (Polynomial IRSProfile.Field)) :=
  G - Polynomial.C (Polynomial.C scale) * liftAffineFamily p₀ p₁

@[simp] theorem eval_liftScalarPolynomial (p : Polynomial IRSProfile.Field)
    (x : IRSProfile.Field) :
    (liftScalarPolynomial p).eval
      (Polynomial.C (Polynomial.C x)) =
        Polynomial.C (Polynomial.C (p.eval x)) := by
  unfold liftScalarPolynomial
  rw [Polynomial.eval_map]
  rw [show Polynomial.C (Polynomial.C x) =
      (((Polynomial.C : Polynomial IRSProfile.Field →+*
        Polynomial (Polynomial IRSProfile.Field)).comp
          (Polynomial.C : IRSProfile.Field →+*
            Polynomial IRSProfile.Field)) x) by rfl]
  rw [Polynomial.eval₂_at_apply]
  rfl

@[simp] theorem eval_liftAffineFamily
    (p₀ p₁ : Polynomial IRSProfile.Field) (x : IRSProfile.Field) :
    (liftAffineFamily p₀ p₁).eval
      (Polynomial.C (Polynomial.C x)) =
        Polynomial.C
          (Polynomial.C (p₀.eval x) + Polynomial.X *
            Polynomial.C (p₁.eval x)) := by
  simp [liftAffineFamily]
  ring

@[simp] theorem map_liftScalarPolynomial
    (p : Polynomial IRSProfile.Field) (z y : IRSProfile.Field) :
    (liftScalarPolynomial p).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) = p := by
  apply Polynomial.ext
  intro i
  simp [liftScalarPolynomial]

@[simp] theorem map_liftAffineFamily
    (p₀ p₁ : Polynomial IRSProfile.Field) (z y : IRSProfile.Field) :
    (liftAffineFamily p₀ p₁).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y) =
        p₀ + Polynomial.C z * p₁ := by
  simp [liftAffineFamily]

theorem natDegree_liftScalarPolynomial_le
    (p : Polynomial IRSProfile.Field) :
    (liftScalarPolynomial p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_map_le

theorem natDegree_liftAffineFamily_le
    (p₀ p₁ : Polynomial IRSProfile.Field) :
    (liftAffineFamily p₀ p₁).natDegree ≤
      max p₀.natDegree p₁.natDegree := by
  unfold liftAffineFamily
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_liftScalarPolynomial_le p₀).trans (Nat.le_max_left _ _)
  · exact Polynomial.natDegree_mul_le.trans (by
      simpa using (natDegree_liftScalarPolynomial_le p₁).trans
        (Nat.le_max_right _ _))

theorem natDegree_universalAlignmentDifference_le
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field)
    (p₀ p₁ : Polynomial IRSProfile.Field) :
    (universalAlignmentDifference G scale p₀ p₁).natDegree ≤
      max G.natDegree (max p₀.natDegree p₁.natDegree) := by
  unfold universalAlignmentDifference
  refine (Polynomial.natDegree_sub_le _ _).trans
    (max_le (Nat.le_max_left _ _) ?_)
  exact Polynomial.natDegree_mul_le.trans (by
    simpa using (natDegree_liftAffineFamily_le p₀ p₁).trans
      (Nat.le_max_right _ _))

/-- Fixed-resultant promotion on every rich coordinate.  Membership in
`richCoordinates ... threshold` says exactly that the corresponding fiber has
more than `threshold` seeds. -/
theorem rich_beta_eq_zero_of_fixed_resultants
    {Seed : Type*} [DecidableEq Seed]
    (good : Finset Seed) (support : Seed → Finset IRSProfile.Index)
    (z : Seed → IRSProfile.Field)
    (hz : Set.InjOn z (good : Set Seed))
    (H : Polynomial (Polynomial IRSProfile.Field))
    (hHirr : Irreducible
      (H.map (algebraMap (Polynomial IRSProfile.Field)
        (FractionRing (Polynomial IRSProfile.Field)))))
    (hHpos : 0 < H.natDegree)
    (yAt : Seed → IRSProfile.Field)
    (hHroot : ∀ seed ∈ good,
      (FiniteTaylorResultantRigidity.specializeZ (z seed) H).eval
        (yAt seed) = 0)
    (beta : IRSProfile.Index →
      Polynomial (Polynomial IRSProfile.Field))
    (hbetaDegree : ∀ i, (beta i).natDegree < H.natDegree)
    (hresultantDegree : ∀ i,
      (quotientResultant H (beta i)).natDegree < 2 ^ 47)
    (hbetaRoot : ∀ i seed,
      i ∈ richCoordinates good support (2 ^ 47) →
      seed ∈ good → i ∈ support seed →
      (FiniteTaylorResultantRigidity.specializeZ (z seed) (beta i)).eval
        (yAt seed) = 0) :
    ∀ i, i ∈ richCoordinates good support (2 ^ 47) → beta i = 0 := by
  classical
  intro i hi
  let fiber := good.filter fun seed => i ∈ support seed
  have hfiberCard : 2 ^ 47 < fiber.card := by
    simpa [fiber, richCoordinates, incidence] using hi
  apply beta_eq_zero_of_many_common_roots fiber z
    (hz.mono (by
      intro seed hseed
      exact (Finset.mem_filter.mp hseed).1))
    H (beta i) hHirr hHpos (hbetaDegree i)
    ((hresultantDegree i).trans hfiberCard) yAt
  · intro seed hseed
    exact hHroot seed (Finset.mem_filter.mp hseed).1
  · intro seed hseed
    have hs := Finset.mem_filter.mp hseed
    exact hbetaRoot i seed hi hs.1 hs.2

/-- Abstract final assembly.  `hbetaZero` is precisely the output of the
rich-fiber fixed-resultant argument.  `hGseed` is precisely the polynomial
identity supplied by finite Taylor extraction at every retained seed.

No quotient evaluation is treated as injective: quotient congruences at the
interpolation nodes are first promoted coefficientwise, and only then
evaluated at each specialized root.
-/
theorem selectedPolynomialAlignment_of_rich_quotient_data
    {rows : Fin 2 → IRSProfile.Index → IRSProfile.Field}
    {bad good : Finset IRSProfile.Field}
    (selected : ∀ gamma : {gamma : IRSProfile.Field // gamma ∈ bad},
      TargetBadSeedWitness rows gamma.1)
    (hgoodSub : good ⊆ bad)
    (hgoodCard : 2 ^ 50 < good.card)
    (H : Polynomial (Polynomial IRSProfile.Field))
    (G : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (scale : Polynomial IRSProfile.Field)
    (yAt : IRSProfile.Field → IRSProfile.Field)
    (hHroot : ∀ gamma ∈ good,
      (H.map (Polynomial.evalRingHom gamma)).eval (yAt gamma) = 0)
    (hscale : ∀ gamma ∈ good, scale.eval gamma ≠ 0)
    (hGdegree : G.natDegree ≤ 131071)
    (hGseed : ∀ gamma, ∀ hgamma : gamma ∈ good,
      G.map (Polynomial.eval₂RingHom (Polynomial.evalRingHom gamma)
          (yAt gamma)) =
        Polynomial.C (scale.eval gamma) *
          (selected ⟨gamma, hgoodSub hgamma⟩).polynomial)
    (support : IRSProfile.Field → Finset IRSProfile.Index)
    (hsupportEq : ∀ gamma, ∀ hgamma : gamma ∈ good,
      support gamma = (selected ⟨gamma, hgoodSub hgamma⟩).support)
    (hbetaZero : ∀ i,
      i ∈ richCoordinates good support (2 ^ 47) →
      canonicalRemainder H
        (G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain i))) -
          Polynomial.C
            (scale * (Polynomial.C (rows 0 i) +
              Polynomial.X * Polynomial.C (rows 1 i)))) = 0) :
    ∃ p₀ p₁ : Polynomial IRSProfile.Field,
      p₀.degree < IRSProfile.baseDimension ∧
      p₁.degree < IRSProfile.baseDimension ∧
      ∃ aligned : Finset IRSProfile.Field,
        ∃ alignedSub : aligned ⊆ bad,
          Fintype.card IRSProfile.Index + 1 ≤ aligned.card ∧
          ∀ gamma, ∀ hgamma : gamma ∈ aligned,
            (selected ⟨gamma, alignedSub hgamma⟩).polynomial =
              p₀ + Polynomial.C gamma * p₁ := by
  classical
  let rich := richCoordinates good support (2 ^ 47)
  have hsupport : ∀ gamma ∈ good, 196592 ≤ (support gamma).card := by
    intro gamma hgamma
    rw [hsupportEq gamma hgamma,
      (selected ⟨gamma, hgoodSub hgamma⟩).support_card]
  have hrichCard : 131071 < rich.card := by
    dsimp only [rich]
    exact target5314_many_rich_coordinates good support hsupport hgoodCard
  obtain ⟨K, hKrich, hKcard⟩ :=
    Finset.exists_subset_card_eq (s := rich) (n := 131072) (by omega)
  let p₀ : Polynomial IRSProfile.Field :=
    Lagrange.interpolate K IRSProfile.domain (rows 0)
  let p₁ : Polynomial IRSProfile.Field :=
    Lagrange.interpolate K IRSProfile.domain (rows 1)
  have hp₀degree : p₀.degree < IRSProfile.baseDimension := by
    rw [show IRSProfile.baseDimension = 131072 by
      norm_num [IRSProfile.baseDimension], ← hKcard]
    exact Lagrange.degree_interpolate_lt (rows 0)
      IRSProfile.domain.injective.injOn
  have hp₁degree : p₁.degree < IRSProfile.baseDimension := by
    rw [show IRSProfile.baseDimension = 131072 by
      norm_num [IRSProfile.baseDimension], ← hKcard]
    exact Lagrange.degree_interpolate_lt (rows 1)
      IRSProfile.domain.injective.injOn
  have hp₀nat : p₀.natDegree ≤ 131071 := by
    by_cases hp : p₀ = 0
    · simp [hp]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hp₀degree
      norm_num [IRSProfile.baseDimension] at this ⊢
      omega
  have hp₁nat : p₁.natDegree ≤ 131071 := by
    by_cases hp : p₁ = 0
    · simp [hp]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hp₁degree
      norm_num [IRSProfile.baseDimension] at this ⊢
      omega
  let D := universalAlignmentDifference G scale p₀ p₁
  have hDdegree : D.natDegree < Fintype.card {i // i ∈ K} := by
    rw [Fintype.card_coe, hKcard]
    exact (natDegree_universalAlignmentDifference_le G scale p₀ p₁).trans_lt
      (by omega)
  have hDpoint : ∀ ii : {i // i ∈ K},
      canonicalRemainder H
        (D.eval (Polynomial.C (Polynomial.C (IRSProfile.domain ii.1)))) = 0 := by
    intro ii
    have hiRich : ii.1 ∈ rich := hKrich ii.2
    have hp₀eval : p₀.eval (IRSProfile.domain ii.1) = rows 0 ii.1 :=
      Lagrange.eval_interpolate_at_node (rows 0)
        IRSProfile.domain.injective.injOn ii.2
    have hp₁eval : p₁.eval (IRSProfile.domain ii.1) = rows 1 ii.1 :=
      Lagrange.eval_interpolate_at_node (rows 1)
        IRSProfile.domain.injective.injOn ii.2
    have hb := hbetaZero ii.1 (by
      simpa [rich] using hiRich)
    have hDeval :
        D.eval (Polynomial.C (Polynomial.C (IRSProfile.domain ii.1))) =
          G.eval (Polynomial.C (Polynomial.C (IRSProfile.domain ii.1))) -
            Polynomial.C
              (scale * (Polynomial.C (rows 0 ii.1) +
                Polynomial.X * Polynomial.C (rows 1 ii.1))) := by
      simp only [D, universalAlignmentDifference, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, eval_liftAffineFamily,
        hp₀eval, hp₁eval]
      congr 1
      simp
    rw [hDeval]
    exact hb
  have hDrem : coefficientwiseRemainder H D = 0 := by
    apply coefficientwiseRemainder_eq_zero_of_many_evaluations
      (fun ii : {i // i ∈ K} => IRSProfile.domain ii.1)
    · intro i j hij
      exact Subtype.ext (IRSProfile.domain.injective hij)
    · exact hDdegree
    · exact hDpoint
  have halignGood : ∀ gamma, ∀ hgamma : gamma ∈ good,
      (selected ⟨gamma, hgoodSub hgamma⟩).polynomial =
        p₀ + Polynomial.C gamma * p₁ := by
    intro gamma hgamma
    have hDmap :=
      map_at_specialized_root_eq_zero_of_coefficientwiseRemainder_eq_zero
        H D hDrem gamma (yAt gamma) (hHroot gamma hgamma)
    change (universalAlignmentDifference G scale p₀ p₁).map
      (Polynomial.eval₂RingHom (Polynomial.evalRingHom gamma) (yAt gamma)) = 0
      at hDmap
    simp only [universalAlignmentDifference, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, map_liftAffineFamily] at hDmap
    rw [hGseed gamma hgamma] at hDmap
    have hdiff :
        Polynomial.C (scale.eval gamma) *
          (selected ⟨gamma, hgoodSub hgamma⟩).polynomial -
        Polynomial.C (scale.eval gamma) *
          (p₀ + Polynomial.C gamma * p₁) = 0 := by
      simpa [D, universalAlignmentDifference] using hDmap
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (hscale gamma hgamma))
    exact sub_eq_zero.mp hdiff
  refine ⟨p₀, p₁, hp₀degree, hp₁degree, good, hgoodSub, ?_, ?_⟩
  · have hindex : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hindex]
    omega
  · intro gamma hgamma
    exact halignGood gamma hgamma

end

end ProximityPrize.SubmissionLower.FiniteTaylorAlignmentAssembly
