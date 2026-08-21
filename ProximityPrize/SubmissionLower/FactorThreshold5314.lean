import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.FactorThreshold5314

/-- Size retained after the two `/11` factor pigeonholes.  The extra `2^45`
is reserved for the leading-coefficient, determinant, and separability
exceptional seeds. -/
def branchThreshold : ℕ := 2 ^ 50 + 2 ^ 45

theorem two_factor_pigeonhole_budget :
    11 * (11 * branchThreshold + 72) + 72 < 2 ^ 57 := by
  norm_num [branchThreshold]

theorem branch_survives_exception_budget {branch exceptions : ℕ}
    (hbranch : branchThreshold < branch) (hexceptions : exceptions < 2 ^ 45) :
    2 ^ 50 < branch - exceptions := by
  simp only [branchThreshold] at hbranch
  omega

theorem aligned_card_budget {branch exceptions : ℕ}
    (hbranch : branchThreshold < branch) (hexceptions : exceptions < 2 ^ 45) :
    262145 ≤ branch - exceptions := by
  have := branch_survives_exception_budget hbranch hexceptions
  omega

end ProximityPrize.SubmissionLower.FactorThreshold5314
