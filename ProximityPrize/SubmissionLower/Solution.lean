import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSFinal6400

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6400 307121 1048576 := by
  apply ProximityPrize.SubmissionLower.protocolClaim6400_of_alignment
  sorry

end ProximityPrize.Benchmark
