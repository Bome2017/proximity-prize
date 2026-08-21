import ProximityPrize.SubmissionLower.BCHKSUnconditionalAlignment
import ProximityPrize.SubmissionLower.BCHKSFinalConditional

namespace ProximityPrize.Benchmark

theorem protocolClaim6392 : ProtocolClaim 6392 306815 1048576 :=
  protocolClaim6392_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment

end ProximityPrize.Benchmark
