import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Finset

/-- Generic exact arithmetic closure for an integral Johnson count. -/
lemma integral_counting_contradiction
    (inc pairs M A C K N D : ℕ)
    (hinc : M * A ≤ inc)
    (htangent : C * inc ≤ pairs + K * N)
    (hpairs : pairs ≤ M * (M - 1) * D)
    (hgap : M * (M - 1) * D + K * N < C * (M * A)) : False := by
  nlinarith

/-- Universal integral tangent to `m ↦ m(m-1)` at the adjacent integers
`q` and `q+1`.  This is the discrete convexity step behind exact Johnson bounds. -/
lemma integral_tangent (q m : ℕ) :
    2 * q * m ≤ m * (m - 1) + q * (q + 1) := by
  by_cases hm0 : m = 0
  · simp [hm0]
  have hm1 : 1 ≤ m := by omega
  have hi : (2 * q : ℤ) * m ≤ m * (m - 1) + q * (q + 1) := by
    by_cases h : m ≤ q
    · have h1 : (0 : ℤ) ≤ q - m := by omega
      have h2 : (0 : ℤ) ≤ q + 1 - m := by omega
      nlinarith [mul_nonneg h1 h2]
    · have h1 : (0 : ℤ) ≤ m - q := by omega
      have h2 : (0 : ℤ) ≤ m - (q + 1) := by omega
      nlinarith [mul_nonneg h1 h2]
  exact_mod_cast hi

/-- Integer tangent at the active 63.99 average multiplicity. -/
lemma integral_tangent_6399 (m : ℕ) :
    4978 * m ≤ m * (m - 1) + 6197610 := by
  simpa using integral_tangent 2489 m

/-- Final exact numerical contradiction for a 3520-word family at radius 76770. -/
lemma integral_3520_contradiction
    (inc pairs : ℕ) (hinc : 652516480 ≤ inc)
    (htangent : 4978 * inc ≤ pairs + 6197610 * 262144)
    (hpairs : pairs ≤ 3520 * 3519 * 131071) : False := by
  apply integral_counting_contradiction inc pairs 3520 185374 4978 6197610
    262144 131071
  · exact hinc
  · exact htangent
  · exact hpairs
  · norm_num

end ProximityPrize.SubmissionLower
