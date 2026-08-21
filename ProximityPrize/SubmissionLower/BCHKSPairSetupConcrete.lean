import ProximityPrize.SubmissionLower.BCHKSPairSetup
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower

open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Turn a pair of selected normalized factors into all the algebraic, degree,
and Hensel data used by the BCHKS argument.  In particular, both sharp support
bounds for `R` are inherited from `Q`, rather than being additional hypotheses
on the selected factor. -/
theorem bchks_pair_setup_of_selected_factors
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hQ : Q ≠ 0)
    (hRQ : R ∈ UniqueFactorizationMonoid.normalizedFactors Q)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hQY : Q.natDegree ≤ 255)
    (hQYZ : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < 63302)
    (hQweightedX : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 33398999)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible R ∧ Irreducible H ∧ 0 < H.natDegree ∧
    H ∣ triSpecializeX R x₀ ∧
    R.natDegree ≤ 255 ∧ H.natDegree ≤ 255 ∧
    Polynomial.Bivariate.totalDegree H ≤ 63302 ∧
    Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 63302 ∧
    (∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 33398999) ∧
    RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
  have hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 63302 :=
    YZFactorCap.normalizedFactor_YZ_cap Q R 63302 hQ hRQ hQYZ
  have hRweightedX : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 33398999 :=
    WeightedFactorCaps.normalizedFactor_weightedX_cap
      Q R 131071 33398999 hQ hRQ hQweightedX
  exact setup_selected_pair Q R H x₀ hQ hRQ hHR hHpos hQY hRYZ
    hRweightedX hprim

end ProximityPrize.SubmissionLower
