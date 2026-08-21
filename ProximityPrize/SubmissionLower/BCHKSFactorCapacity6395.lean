import ProximityPrize.SubmissionLower.BCHKSStagedArithmetic
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower

/-- Effective square mass for mixed linear/nonlinear factor accounting. -/
def factorEffectiveMass (linearWeight d : Nat) : Nat :=
  if d = 1 then linearWeight else d ^ 2

/-- A factor-dependent staged capacity is controlled by effective square
mass: linear factors consume `linearWeight`, while nonlinear factors consume
their squared degree. -/
theorem sum_mixed_capacities_le_of_effective_mass
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ)
    (d bad : ρ → Nat) (L A linearWeight e DZ yCap S : Nat)
    (hlinear : L ≤ A * linearWeight)
    (hmass : (∑ r ∈ Rs, factorEffectiveMass linearWeight (d r)) ≤ S)
    (hdsum : (∑ r ∈ Rs, d r) ≤ yCap)
    (hbad : ∀ r ∈ Rs, bad r ≤ 2 * d r * DZ) :
    (∑ r ∈ Rs,
      ((if d r = 1 then L else A * d r) * d r + e * d r + bad r)) ≤
        A * S + e * yCap + 2 * DZ * yCap := by
  have hpoint : ∀ r ∈ Rs,
      (if d r = 1 then L else A * d r) * d r + e * d r + bad r ≤
        A * factorEffectiveMass linearWeight (d r) + e * d r + 2 * DZ * d r := by
    intro r hr
    have hpair : (if d r = 1 then L else A * d r) * d r ≤
        A * factorEffectiveMass linearWeight (d r) := by
      by_cases hOne : d r = 1
      · simp [hOne, factorEffectiveMass, hlinear]
      · simp [hOne, factorEffectiveMass, pow_two, Nat.mul_assoc]
    have hbad' : bad r ≤ 2 * DZ * d r := by
      calc
        bad r ≤ 2 * d r * DZ := hbad r hr
        _ = 2 * DZ * d r := by ring
    exact Nat.add_le_add (Nat.add_le_add hpair (le_refl _)) hbad'
  calc
    (∑ r ∈ Rs,
      ((if d r = 1 then L else A * d r) * d r + e * d r + bad r)) ≤
        ∑ r ∈ Rs,
          (A * factorEffectiveMass linearWeight (d r) +
            e * d r + 2 * DZ * d r) := Finset.sum_le_sum hpoint
    _ = A * (∑ r ∈ Rs, factorEffectiveMass linearWeight (d r)) +
          e * (∑ r ∈ Rs, d r) + 2 * DZ * (∑ r ∈ Rs, d r) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A * S + e * yCap + 2 * DZ * yCap := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left A hmass) (Nat.mul_le_mul_left e hdsum))
        (Nat.mul_le_mul_left (2 * DZ) hdsum)

/-- Numerical 63.95 capacity checkpoint for the prospective interpolation
box `(m,DX,DY,DZ) = (708,131273112,1002,719912)`. -/
theorem bchks_6395_effective_capacity :
    (632281 * 719911) * 604104 +
      (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 <
        274980000000000000 := by
  norm_num

/-- The linear branch fits the common effective-mass unit with weight 416. -/
theorem bchks_6395_linear_weight :
    2 * 131273112 * 719911 ≤ (632281 * 719911) * 416 := by
  norm_num

/-- Exact arithmetic dichotomy for 63.95.  Either the effective mass fits the
field budget, or there is one dominant factor of degree at least 689 and the
total degree of every other factor is at most 312. -/
theorem bchks_6395_effective_mass_or_dominant
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ) (d : ρ → Nat)
    (hSum : (∑ r ∈ Rs, d r) ≤ 1001) :
    (∑ r ∈ Rs, factorEffectiveMass 416 (d r)) ≤ 604104 ∨
      ∃ r₀ ∈ Rs, 689 ≤ d r₀ ∧
        (∑ r ∈ Rs.erase r₀, d r) ≤ 312 ∧
        ∀ s ∈ Rs, 689 ≤ d s → s = r₀ := by
  by_cases hLarge : ∃ r ∈ Rs, 604 ≤ d r
  · obtain ⟨r₀, hr₀, hr₀Large⟩ := hLarge
    by_cases hDominant : 689 ≤ d r₀
    · right
      refine ⟨r₀, hr₀, hDominant, ?_, ?_⟩
      · have hsplit : (∑ r ∈ Rs.erase r₀, d r) + d r₀ =
            ∑ r ∈ Rs, d r := Finset.sum_erase_add _ _ hr₀
        omega
      · intro s hs hsLarge
        by_contra hne
        have hsErase : s ∈ Rs.erase r₀ :=
          Finset.mem_erase.mpr ⟨hne, hs⟩
        have hsle : d s ≤ ∑ r ∈ Rs.erase r₀, d r :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsErase
        have hsplit : (∑ r ∈ Rs.erase r₀, d r) + d r₀ =
            ∑ r ∈ Rs, d r := Finset.sum_erase_add _ _ hr₀
        omega
    · left
      have hr₀Hi : d r₀ ≤ 688 := by omega
      have hsplitDegree : (∑ r ∈ Rs.erase r₀, d r) + d r₀ =
          ∑ r ∈ Rs, d r := Finset.sum_erase_add _ _ hr₀
      have hremDegree : (∑ r ∈ Rs.erase r₀, d r) ≤ 1001 - d r₀ := by
        omega
      have hremSmall : ∀ s ∈ Rs.erase r₀, d s ≤ 397 := by
        intro s hs
        have hsle : d s ≤ ∑ r ∈ Rs.erase r₀, d r :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
        omega
      have hremPoint : ∀ s ∈ Rs.erase r₀,
          factorEffectiveMass 416 (d s) ≤ 416 * d s := by
        intro s hs
        by_cases hOne : d s = 1
        · simp [factorEffectiveMass, hOne]
        · rw [factorEffectiveMass, if_neg hOne, pow_two]
          exact Nat.mul_le_mul_right (d s) ((hremSmall s hs).trans (by omega))
      have hremMass :
          (∑ s ∈ Rs.erase r₀, factorEffectiveMass 416 (d s)) ≤
            416 * (1001 - d r₀) := by
        calc
          _ ≤ ∑ s ∈ Rs.erase r₀, 416 * d s := Finset.sum_le_sum hremPoint
          _ = 416 * (∑ s ∈ Rs.erase r₀, d s) := by rw [Finset.mul_sum]
          _ ≤ 416 * (1001 - d r₀) := Nat.mul_le_mul_left 416 hremDegree
      have hcurve : d r₀ ^ 2 + 416 * (1001 - d r₀) ≤ 603552 := by
        interval_cases hd : d r₀ <;> norm_num [hd]
      have hsplitMass :
          (∑ s ∈ Rs.erase r₀, factorEffectiveMass 416 (d s)) +
              factorEffectiveMass 416 (d r₀) =
            ∑ s ∈ Rs, factorEffectiveMass 416 (d s) :=
        Finset.sum_erase_add _ _ hr₀
      rw [← hsplitMass]
      have hrNotOne : d r₀ ≠ 1 := by omega
      rw [factorEffectiveMass, if_neg hrNotOne]
      omega
  · left
    push Not at hLarge
    have hpoint : ∀ r ∈ Rs,
        factorEffectiveMass 416 (d r) ≤ 603 * d r := by
      intro r hr
      have hd : d r ≤ 603 := by
        have := hLarge r hr
        omega
      by_cases hOne : d r = 1
      · simp [factorEffectiveMass, hOne]
      · rw [factorEffectiveMass, if_neg hOne, pow_two]
        exact Nat.mul_le_mul_right (d r) hd
    calc
      (∑ r ∈ Rs, factorEffectiveMass 416 (d r)) ≤
          ∑ r ∈ Rs, 603 * d r := Finset.sum_le_sum hpoint
      _ = 603 * (∑ r ∈ Rs, d r) := by rw [Finset.mul_sum]
      _ ≤ 603 * 1001 := Nat.mul_le_mul_left 603 hSum
      _ ≤ 604104 := by norm_num

/-- Normalized-factor form of the 63.95 dichotomy. -/
theorem bchks_6395_normalized_factor_dichotomy
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hQdeg : Q.natDegree ≤ 1001) :
    let Rs := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
      (fun R => 0 < R.natDegree)
    (∑ R ∈ Rs, factorEffectiveMass 416 R.natDegree) ≤ 604104 ∨
      ∃ R₀ ∈ Rs, 689 ≤ R₀.natDegree ∧
        (∑ R ∈ Rs.erase R₀, R.natDegree) ≤ 312 ∧
        ∀ H ∈ Rs, 689 ≤ H.natDegree → H = R₀ := by
  dsimp
  apply bchks_6395_effective_mass_or_dominant
  calc
    (∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun R => 0 < R.natDegree), R.natDegree) ≤
      ∑ R ∈ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset,
        R.natDegree := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
    _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
    _ ≤ 1001 := hQdeg

/-- The exceptional factor has a genuinely small ambient cofactor, not merely
a small complement in the factor-degree sum.  Exact multiplicativity of both
weighted support functions preserves the quantitative savings needed by a
cofactor-aware alignment argument. -/
theorem bchks_6395_dominant_ambient_cofactor
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hQdeg : Q.natDegree ≤ 1001)
    (hRlarge : 689 ≤ R.natDegree)
    (hQweighted : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 131273112)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 719912) :
    ∃ C, Q = R * C ∧ C ≠ 0 ∧ C.natDegree ≤ 312 ∧
      WeightedFactorCaps.weightedSupportDegree C 131071 < 40965193 ∧
      YZFactorCap.yzSupportDegree C 1 < 719223 := by
  classical
  obtain ⟨C, hfac⟩ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hRQ
  have hprod : R * C ≠ 0 := by simpa [← hfac] using hQ
  have hne : R ≠ 0 ∧ C ≠ 0 := mul_ne_zero_iff.mp hprod
  have hdegEq : Q.natDegree = R.natDegree + C.natDegree := by
    rw [hfac, Polynomial.natDegree_mul hne.1 hne.2]
  have hCdeg : C.natDegree ≤ 312 := by omega
  have hQweight :
      WeightedFactorCaps.weightedSupportDegree Q 131071 < 131273112 :=
    WeightedFactorCaps.weightedSupportDegree_lt_of_coeff_cap
      Q 131071 131273112 hQ hQweighted
  have hweightSum :
      WeightedFactorCaps.weightedSupportDegree R 131071 +
          WeightedFactorCaps.weightedSupportDegree C 131071 < 131273112 := by
    rw [hfac, WeightedFactorCaps.weightedSupportDegree_mul R C 131071 hne.1 hne.2]
      at hQweight
    exact hQweight
  have hRweight : 131071 * R.natDegree ≤
      WeightedFactorCaps.weightedSupportDegree R 131071 := by
    have hlead := WeightedFactorCaps.coeffWeight_le_of_ne R 131071 R.natDegree
      (by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hne.1)
    omega
  have hCweight :
      WeightedFactorCaps.weightedSupportDegree C 131071 < 40965193 := by
    omega
  have hQyz : YZFactorCap.yzSupportDegree Q 1 < 719912 := by
    unfold YZFactorCap.yzSupportDegree
    rw [Finset.sup_lt_iff (by norm_num)]
    intro j hj
    have hcoeff : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    obtain ⟨a, ha, hadeg, -⟩ :=
      Polynomial.Bivariate.exists_max_index_degreeX (Q.coeff j) hcoeff
    have hca : (Q.coeff j).coeff a ≠ 0 := Polynomial.mem_support_iff.mp ha
    simpa [hadeg] using hQYZ j a hca
  have hyzSum :
      YZFactorCap.yzSupportDegree R 1 +
          YZFactorCap.yzSupportDegree C 1 < 719912 := by
    rw [hfac, YZFactorCap.yzSupportDegree_mul R C 1 hne.1 hne.2] at hQyz
    exact hQyz
  have hRyz : R.natDegree ≤ YZFactorCap.yzSupportDegree R 1 := by
    have hlead := YZFactorCap.coeffWeight_le_of_ne R 1 R.natDegree
      (by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hne.1)
    omega
  have hCyz : YZFactorCap.yzSupportDegree C 1 < 719223 := by omega
  exact ⟨C, hfac, hne.2, hCdeg, hCweight, hCyz⟩

/-- Numerical target for the cofactor-aware exceptional branch.  If the
dominant factor of degree `d` and its entire complementary part of degree `c`
can be charged together by `d * (c + 416)` effective units, the 63.95
numerator fits for every possible dominant split. -/
theorem bchks_6395_dominant_cofactor_capacity
    (d c : Nat) (hd : 689 ≤ d) (hsum : d + c ≤ 1001) :
    (632281 * 719911) * (d * (c + 416)) +
        (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 <
      274980000000000000 := by
  have hdHi : d ≤ 1001 := by omega
  have hc : c ≤ 1001 - d := by omega
  calc
    (632281 * 719911) * (d * (c + 416)) +
          (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 ≤
        (632281 * 719911) * (d * ((1001 - d) + 416)) +
          (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 := by
      gcongr
    _ < 274980000000000000 := by
      interval_cases d <;> norm_num

/-- Every normalized-factor configuration in the regular branch fits the
full 63.95 staged numerator, including the one-time bad-Z deletion. -/
theorem bchks_6395_regular_factor_capacity
    {ρ : Type*} [DecidableEq ρ] (Rs : Finset ρ)
    (d bad : ρ → Nat)
    (hmass : (∑ r ∈ Rs, factorEffectiveMass 416 (d r)) ≤ 604104)
    (hdsum : (∑ r ∈ Rs, d r) ≤ 1001)
    (hbad : ∀ r ∈ Rs, bad r ≤ 2 * d r * 719912) :
    (∑ r ∈ Rs,
      ((if d r = 1 then 2 * 131273112 * 719911
        else (632281 * 719911) * d r) * d r +
          (76730 + 1) * d r + bad r)) + 719912 <
        274980000000000000 := by
  have hcap := sum_mixed_capacities_le_of_effective_mass Rs d bad
    (2 * 131273112 * 719911) (632281 * 719911) 416
    (76730 + 1) 719912 1001 604104 bchks_6395_linear_weight hmass hdsum hbad
  calc
    _ ≤ (632281 * 719911) * 604104 +
        (76730 + 1) * 1001 + 2 * 719912 * 1001 + 719912 :=
      Nat.add_le_add_right hcap _
    _ < 274980000000000000 := bchks_6395_effective_capacity

end ProximityPrize.SubmissionLower
