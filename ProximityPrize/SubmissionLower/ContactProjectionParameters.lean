import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentParameters

/-!
# Characteristic-safe coordinate-projection budgets

Model label: gpt-5.

The frozen contact witness's own coordinate-degree vector.  The strict
characteristic comparisons that used to live here are gone: the planar
bidegree bound is now proved from resultant multiplicity
(`PlaneNoSeparableDegree`, `PlaneNoSeparableFamily`) rather than from an
embedding count, so no projection degree has to stay below the
characteristic.
-/

namespace ProximityPrize.SubmissionLower.ContactProjectionParameters

open ContactAlignmentParameters

def surfaceVector : DegreeVector := ⟨yCap, slopeCap, seedTotalCap⟩

end ProximityPrize.SubmissionLower.ContactProjectionParameters
