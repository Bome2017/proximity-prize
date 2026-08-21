import ProximityPrize.SubmissionLower.BCHKSUnconditionalAlignment
import ProximityPrize.SubmissionLower.BCHKSFinalConditional

namespace ProximityPrize.Benchmark

theorem protocolClaim6358 : ProtocolClaim 6358 305433 1048576 :=
  protocolClaim6358_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment

end ProximityPrize.Benchmark
