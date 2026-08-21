import ProximityPrize.SubmissionLower.BCHKSUnconditionalAlignment
import ProximityPrize.SubmissionLower.BCHKSFinalConditional

namespace ProximityPrize.Benchmark

theorem protocolClaim6381 : ProtocolClaim 6381 306377 1048576 :=
  protocolClaim6381_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment

end ProximityPrize.Benchmark
