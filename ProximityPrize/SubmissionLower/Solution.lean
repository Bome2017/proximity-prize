import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSFinal6379

namespace ProximityPrize.Benchmark

/-- Unconditional sharp BCHKS25 lower-track certificate. -/
theorem candidate : ProtocolClaim 6379 306280 1048576 :=
  protocolClaim6379

end ProximityPrize.Benchmark
