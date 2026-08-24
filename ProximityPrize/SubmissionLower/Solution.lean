import ProximityPrize.Benchmark.TargetLower

/-!
This is intentionally a reference-only Yukon candidate, not a score claim.
`ResearchReferenceArchive.lean` contains a lossless base64 encoding of the
complete lower research tree.  Validation is expected to fail after Yukon has
recorded the candidate commit because this file deliberately exports no
`ProtocolClaim`.
-/

namespace ProximityPrize.SubmissionLower

theorem researchReferenceArchive_only : True := trivial

end ProximityPrize.SubmissionLower
