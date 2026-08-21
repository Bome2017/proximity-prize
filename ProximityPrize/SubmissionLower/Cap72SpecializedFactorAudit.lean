import ProximityPrize.SubmissionLower.Cap72FactorAudit

namespace ProximityPrize.SubmissionLower.Cap72SpecializedFactorAudit

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower
open Cap72FactorAudit

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.constructorNameAsVariable false

noncomputable section

/-- Mapping the coefficient ring of a bivariate polynomial cannot increase
its total degree. -/
theorem totalDegree_map_le
    {A B : Type} [Semiring A] [Semiring B] (f : A →+* B)
    (P : Polynomial (Polynomial A)) :
    Polynomial.Bivariate.totalDegree
      (P.map (Polynomial.mapRingHom f)) ≤
        Polynomial.Bivariate.totalDegree P := by
  classical
  unfold Polynomial.Bivariate.totalDegree
  apply Finset.sup_le
  intro i hi
  have hcoeff0 : (P.map (Polynomial.mapRingHom f)).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hiP : i ∈ P.support := by
    apply Polynomial.mem_support_iff.mpr
    intro hzero
    apply hcoeff0
    simp [hzero]
  have hdegree :
      ((P.map (Polynomial.mapRingHom f)).coeff i).natDegree ≤
        (P.coeff i).natDegree := by
    rw [Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le
  exact (Nat.add_le_add_right hdegree i).trans
    (Finset.le_sup (f := fun j => (P.coeff j).natDegree + j) hiP)

theorem specializeX_eq_map_swapZX
    {F : Type} [Field F] (x : F)
    (R : Polynomial (Polynomial (Polynomial F))) :
    SequentialFactorSelection.specializeX x R =
      (swapZX R).map
        (Polynomial.mapRingHom (Polynomial.evalRingHom x)) := by
  apply Polynomial.ext
  intro y
  change
    (R.map (Polynomial.evalRingHom (Polynomial.C x))).coeff y =
      ((R.map (Polynomial.Bivariate.swap (R := F))).map
        (Polynomial.mapRingHom (Polynomial.evalRingHom x))).coeff y
  rw [Polynomial.coeff_map, Polynomial.coeff_map,
    Polynomial.coeff_map]
  change (Polynomial.evalRingHom (Polynomial.C x)) (R.coeff y) =
    ((Polynomial.Bivariate.swap (R := F)) (R.coeff y)).map
      (Polynomial.evalRingHom x)
  simpa [Polynomial.aeval_def] using
    (Polynomial.Bivariate.aveal_eq_map_swap x (R.coeff y))

theorem specializeX_totalDegree_le_seventyTwo
    {F : Type} [Field F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) (x : F) :
    Polynomial.Bivariate.totalDegree
      (SequentialFactorSelection.specializeX x R) ≤ 72 := by
  rw [specializeX_eq_map_swapZX]
  exact (totalDegree_map_le (Polynomial.evalRingHom x) (swapZX R)).trans
    (factor_totalDegree_swapZX_le Q hR hR0)

theorem specialized_normalizedFactor_totalDegree_le_seventyTwo
    {F : Type} [Field F] [DecidableEq F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) (x : F)
    {H : Polynomial (Polynomial F)}
    (hH : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (SequentialFactorSelection.specializeX x R))
    (hP0 : SequentialFactorSelection.specializeX x R ≠ 0) :
    Polynomial.Bivariate.totalDegree H ≤ 72 := by
  have hHdvd : H ∣ SequentialFactorSelection.specializeX x R :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hH
  obtain ⟨K, hP⟩ := hHdvd
  have hH0 : H ≠ 0 := by
    intro hzero
    subst H
    exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors _ hH
  have hK0 : K ≠ 0 := by
    intro hzero
    apply hP0
    rw [hzero, mul_zero] at hP
    exact hP
  have hexact := Polynomial.Bivariate.totalDegree_mul
    (F := F) hH0 hK0
  rw [← hP] at hexact
  calc
    Polynomial.Bivariate.totalDegree H
        ≤ Polynomial.Bivariate.totalDegree H +
            Polynomial.Bivariate.totalDegree K := Nat.le_add_right _ _
    _ = Polynomial.Bivariate.totalDegree
          (SequentialFactorSelection.specializeX x R) := hexact.symm
    _ ≤ 72 := specializeX_totalDegree_le_seventyTwo Q hR hR0 x

theorem specialized_normalizedFactor_coeff_natDegree_le_seventyTwo
    {F : Type} [Field F] [DecidableEq F]
    {domain : IRSProfile.Index → F} {u v : IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R ∣ Q.polynomial) (hR0 : R ≠ 0) (x : F)
    {H : Polynomial (Polynomial F)}
    (hH : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (SequentialFactorSelection.specializeX x R))
    (hP0 : SequentialFactorSelection.specializeX x R ≠ 0)
    (i : ℕ) : (H.coeff i).natDegree ≤ 72 := by
  rcases Polynomial.Bivariate.coeff_totalDegree_le' H i with h | h
  · exact (Nat.le_add_right _ _).trans
      (h.trans (specialized_normalizedFactor_totalDegree_le_seventyTwo
        Q hR hR0 x hH hP0))
  · simp [h]

/-- Choose a good `X`-specialization and then perform the second `/11`
pigeonhole.  The root ordinate may depend on the chosen `x₀`; in the intended
application it is `p_seed.eval x₀`. -/
theorem exists_good_specialization_and_fixed_factor_cap72
    {Seed : Type} [DecidableEq Seed]
    {domain : IRSProfile.Index → IRSProfile.Field}
    {u v : IRSProfile.Index → IRSProfile.Field}
    (Q : Cap72.Interpolant domain u v)
    (R : Polynomial (Polynomial (Polynomial IRSProfile.Field)))
    (hRmem : R ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial)
    (hpositive : 0 < R.natDegree)
    (seeds : Finset Seed) (z : Seed → IRSProfile.Field)
    (yAt : IRSProfile.Field → Seed → IRSProfile.Field)
    (hz : Set.InjOn z (seeds : Set Seed))
    (hroot : ∀ x₀, ∀ seed ∈ seeds,
      SequentialFactorSelection.evalZY (z seed) (yAt x₀ seed)
        (SequentialFactorSelection.specializeX x₀ R) = 0)
    {threshold : ℕ}
    (hlarge : 11 * threshold + 72 < seeds.card) :
    ∃ x₀ ∈ (Finset.univ : Finset IRSProfile.Field),
      (SequentialFactorSelection.specializeX x₀ R).natDegree = R.natDegree ∧
      (SequentialFactorSelection.derivativeResultant R).eval
        (Polynomial.C x₀) ≠ 0 ∧
      ∃ H : Polynomial (Polynomial IRSProfile.Field),
        H ∈ UniqueFactorizationMonoid.normalizedFactors
          (SequentialFactorSelection.specializeX x₀ R) ∧
        Irreducible H ∧
        0 < H.natDegree ∧
        H.natDegree ≤ 11 ∧
        (∀ i, (H.coeff i).natDegree ≤ 72) ∧
        H ∣ SequentialFactorSelection.specializeX x₀ R ∧
        (SequentialFactorSelection.fractionMap
          (SequentialFactorSelection.specializeX x₀ R)).Separable ∧
        (SequentialFactorSelection.fractionMap H).Separable ∧
        threshold <
          (seeds.filter fun seed =>
            SequentialFactorSelection.evalZY (z seed) (yAt x₀ seed) H = 0).card := by
  classical
  obtain ⟨x₀, hx₀, hdegree, hres⟩ :=
    exists_good_specialization_cap72 Q R hRmem hpositive
  let P := SequentialFactorSelection.specializeX x₀ R
  have hRdvd : R ∣ Q.polynomial :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRmem
  have hR0 : R ≠ 0 := by
    intro hzero
    apply UniqueFactorizationMonoid.zero_notMem_normalizedFactors Q.polynomial
    simpa [hzero] using hRmem
  have hPdegree : P.natDegree = R.natDegree := hdegree
  have hP0 : P ≠ 0 := by
    intro hzero
    have : P.natDegree = 0 := by simp [hzero]
    rw [hPdegree] at this
    omega
  have hYdegree : P.natDegree ≤ 11 := by
    rw [hPdegree]
    exact factor_natDegree_le_eleven Q hRdvd
  have hseparable : (SequentialFactorSelection.fractionMap P).Separable :=
    SequentialFactorSelection.fractionMap_specializeX_separable
      R x₀ hpositive hres
  have hfactorHeight : ∀ H,
      H ∈ UniqueFactorizationMonoid.normalizedFactors P →
      0 < H.natDegree → ∀ i, (H.coeff i).natDegree ≤ 72 := by
    intro H hH _hHpos i
    exact specialized_normalizedFactor_coeff_natDegree_le_seventyTwo
      Q hRdvd hR0 x₀ hH hP0 i
  let witnessIndex := P.natDegree
  have hwitness : P.coeff witnessIndex ≠ 0 := by
    simpa [witnessIndex] using Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hwitnessDegree : (P.coeff witnessIndex).natDegree ≤ 72 := by
    have htotal := specializeX_totalDegree_le_seventyTwo Q hRdvd hR0 x₀
    have hcontrib := Polynomial.Bivariate.coeff_totalDegree_le P
      (Polynomial.mem_support_iff.mpr hwitness)
    exact (Nat.le_add_right _ _).trans (hcontrib.trans htotal)
  obtain ⟨H, hHmem, hHirr, hHpos, hHdeg, hHheight, hHdvd,
      hHsep, hHmany⟩ :=
    SequentialFactorSelection.exists_fixed_separable_positiveYFactor
      P hP0 hYdegree hseparable hfactorHeight seeds z (yAt x₀) hz
      (hroot x₀) witnessIndex hwitness hwitnessDegree hlarge
  refine ⟨x₀, ?_⟩
  constructor
  · simp
  constructor
  · exact hdegree
  constructor
  · exact hres
  refine ⟨H, ?_⟩
  constructor
  · exact hHmem
  constructor
  · exact hHirr
  constructor
  · exact hHpos
  constructor
  · exact hHdeg
  constructor
  · exact hHheight
  constructor
  · exact hHdvd
  constructor
  · exact hseparable
  constructor
  · exact hHsep
  · exact hHmany

end

end ProximityPrize.SubmissionLower.Cap72SpecializedFactorAudit
