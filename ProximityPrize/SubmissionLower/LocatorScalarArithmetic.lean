import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.E9

namespace ProximityPrize.SubmissionLower.LocatorScalarArithmetic
open ProximityPrize.Benchmark
open RCN279
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80181
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def prime:ℕ:=2130706433
def multiplicity:ℕ:=44
def yTotalCap:ℕ:=60
def slopeCap:ℕ:=13
def weightedCap:ℕ:=multiplicity*agreements
def listBudget:ℕ:=1033000000
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap - 1)
def regularListNumerator:ℕ:=(n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap - 1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=2798537392:=by decide
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=10675:=by decide
theorem nullity_exact:
   coefficientCount weightedCap w yTotalCap slopeCap -
     n*localRankBound multiplicity yTotalCap slopeCap=150192:=by
 rw [coefficient_count_exact,local_rank_exact]
 decide
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap<
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 decide
theorem list_numeric_values:
   agreements=181963 ∧ gap=50892 ∧ weightedCap=8006372 ∧
   singularListCap=1500 ∧ listNumerator=52570477741929 ∧
   listNumerator/gap+1=1032981171 ∧
   listNumerator<1032981171*gap ∧ 1032981171<listBudget:=by decide
theorem list_numerator_fits:listNumerator<listBudget*gap:=by decide
theorem characteristic_gates:0<slopeCap ∧ slopeCap<prime ∧ yTotalCap<prime ∧
   (2*slopeCap - 1)*weightedCap<prime ∧ singularListCap<prime:=by decide
theorem exists_seedless_interpolant (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0 ∧ Q∈globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       RCN119.slopeDifference IRSProfile.Field ^ (multiplicity-r)∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
 rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
end
end ProximityPrize.SubmissionLower.LocatorScalarArithmetic
