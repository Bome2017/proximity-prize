import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6533

/-!
Exact lower-track entrypoint for the characteristic-free common-shear 65.33
assembly.  Source-policy, kernel compilation, and Yukon validation remain
distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6533 312471 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6533.protocolClaim6533

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
