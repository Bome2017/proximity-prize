# Agent instructions

When changing or preparing submissions for the reduction-threshold benchmarks:

1. Treat each challenge as self-contained. A lower submission may import only
   `ProximityPrize.Benchmark.TargetLower` and modules in
   `ProximityPrize.SubmissionLower`; an upper submission may import only
   `ProximityPrize.Benchmark.TargetUpper` and modules in
   `ProximityPrize.SubmissionUpper`. Never cross-import between challenges.
   Ignore the umbrella `ProximityPrize.lean` when preparing a submission; do
   not import `ProximityPrize`.
2. Keep each submission root flat. Put `Solution.lean`, every helper `.lean`
   file, `score.txt`, and the track-specific claim file directly in that root.
   Subdirectories are not allowed.

Keep these rules aligned with `scripts/check-submission-imports.sh` and with
the independent verifier's source policy.
