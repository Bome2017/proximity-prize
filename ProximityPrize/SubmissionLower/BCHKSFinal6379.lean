import ProximityPrize.SubmissionLower.BCHKSUnconditionalAlignment
import ProximityPrize.SubmissionLower.BCHKSFinalConditional

namespace ProximityPrize.Benchmark

theorem protocolClaim6379 : ProtocolClaim 6379 306280 1048576 :=
  protocolClaim6379_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment

end ProximityPrize.Benchmark
