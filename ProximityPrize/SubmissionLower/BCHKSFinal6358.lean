import ProximityPrize.SubmissionLower.BCHKSUnconditionalAlignment
import ProximityPrize.SubmissionLower.BCHKSFinalConditional

namespace ProximityPrize.Benchmark

theorem protocolClaim6395 : ProtocolClaim 6395 306921 1048576 :=
  protocolClaim6395_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment

end ProximityPrize.Benchmark
