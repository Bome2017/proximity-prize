import ProximityPrize.SubmissionLower.Cap72DegreeBounds
import ProximityPrize.SubmissionLower.Cap72FactorSelection
import ProximityPrize.SubmissionLower.FactorThreshold5314

namespace ProximityPrize.SubmissionLower

open Polynomial

namespace Cap72FirstFactor5314

open Cap72 Cap72FactorSelection
open FactorThreshold5314

set_option maxRecDepth 1000000

/-- The first factor pigeonhole, with constants chosen so that a second factor
pigeonhole leaves `branchThreshold = 2^50 + 2^45` seeds. -/
theorem exists_large_first_factor
    {F : Type} [Field F] [DecidableEq F]
    {domain : ProximityPrize.Benchmark.IRSProfile.Index → F}
    {u v : ProximityPrize.Benchmark.IRSProfile.Index → F}
    (Q : Cap72.Interpolant domain u v)
    (seeds : Finset F) (p : F → F[X])
    (hroot : ∀ z ∈ seeds,
      Cap72FactorSelection.specializeAt z (p z) Q.polynomial = 0)
    (hcard : 2 ^ 57 < seeds.card) :
    ∃ factor,
      factor ∈ UniqueFactorizationMonoid.normalizedFactors Q.polynomial ∧
      Irreducible factor ∧
      0 < factor.natDegree ∧
      11 * branchThreshold + 72 <
        (seeds.filter fun z =>
          Cap72FactorSelection.specializeAt z (p z) factor = 0).card := by
  classical
  obtain ⟨y, x, hcoeff, hdegree⟩ :=
    Q.exists_nonzero_coeff_degree_le_seventyTwo
  have hinj : Set.InjOn (fun z : F => z) (seeds : Set F) := by
    intro a ha b hb hab
    exact hab
  apply Cap72FactorSelection.exists_fixed_positiveYFactor_cap72
    Q.polynomial Q.polynomial_ne_zero Q.polynomial_natDegree_le
    seeds (fun z => z) p hinj hroot y x hcoeff hdegree
  exact lt_trans two_factor_pigeonhole_budget hcard

end Cap72FirstFactor5314

end ProximityPrize.SubmissionLower
