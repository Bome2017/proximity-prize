import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research

/-! Exact arithmetic for the conditional 67.31 curve-only YZ row. -/
namespace ProximityPrize.SubmissionLower.ContactMovingParameters6731Research
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagBezout6543Research ContactMovingPositiveLedger6719Research
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def errors : ℕ := 80073
def agreements : ℕ := n-errors
def gap : ℕ := agreements-w
def listBudget : ℕ := 1000000000
def capacity : ℕ := prime^6/2^128
def mcaBudget : ℕ := capacity-listBudget

structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq
def profileA : Profile := ⟨42,22328,11⟩
def profileB : Profile := ⟨78,1205,24⟩
def profileC : Profile := ⟨40,27619,12⟩
def profileABMeet : Profile := ⟨42,1205,11⟩
def profileFinalMeet : Profile := ⟨40,1205,11⟩
namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity*agreements
def yCap (P : Profile) : ℕ := (P.weightedCap-1)/w
def coefficients (P : Profile) : ℕ := coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P : Profile) : ℕ := localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P : Profile) : ℕ := n*P.localRank
def nullity (P : Profile) : ℕ := P.coefficients-P.totalRank
def characteristicCap (P : Profile) : ℕ := (2*P.slopeCap-1)*P.weightedCap
end Profile

theorem base_values : agreements=182071 ∧ gap=51000 ∧
    capacity=274980728111395087 ∧ mcaBudget=274980727111395087 ∧
    mcaBudget+listBudget=capacity := by decide
theorem profileA_coefficients_exact : profileA.coefficients=50123887598533 := by
  change coefficientCount (42*182071) 131071 22328 11=50123887598533
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (42*182071) 131071 22328 11 59 (by decide) (by decide)]
  decide
theorem profileB_coefficients_exact : profileB.coefficients=17970854459800 := by
  change coefficientCount (78*182071) 131071 1205 24=17970854459800
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (78*182071) 131071 1205 24 109 (by decide) (by decide)]
  decide
theorem profileC_coefficients_exact : profileC.coefficients=59261421895221 := by
  change coefficientCount (40*182071) 131071 27619 12=59261421895221
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (40*182071) 131071 27619 12 56 (by decide) (by decide)]
  decide
theorem profileA_rank_exact : profileA.localRank=191207456 := by decide
theorem profileB_rank_exact : profileB.localRank=68553175 := by decide
theorem profileC_rank_exact : profileC.localRank=226064384 := by decide
theorem profile_values :
    profileA.weightedCap=7646982 ∧ profileB.weightedCap=14201538 ∧
    profileC.weightedCap=7282840 ∧ profileA.yCap=58 ∧ profileB.yCap=108 ∧
    profileC.yCap=55 ∧ profileABMeet.yCap=58 ∧ profileFinalMeet.yCap=55 ∧
    profileA.nullity=252869 ∧ profileB.nullity=50952600 ∧ profileC.nullity=15925 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,?_⟩
  · rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,profileA_rank_exact]; decide
  · rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,profileB_rank_exact]; decide
  · rw [Profile.nullity,Profile.totalRank,profileC_coefficients_exact,profileC_rank_exact]; decide
theorem interpolation_gates : profileA.totalRank<profileA.coefficients ∧
    profileB.totalRank<profileB.coefficients ∧ profileC.totalRank<profileC.coefficients := by
  change n*profileA.localRank<profileA.coefficients ∧ n*profileB.localRank<profileB.coefficients ∧
    n*profileC.localRank<profileC.coefficients
  rw [profileA_coefficients_exact,profileA_rank_exact,
    profileB_coefficients_exact,profileB_rank_exact,profileC_coefficients_exact,profileC_rank_exact]
  decide
theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,min profileA.seedCap profileB.seedCap,
      min profileA.slopeCap profileB.slopeCap)=
      (profileABMeet.multiplicity,profileABMeet.seedCap,profileABMeet.slopeCap) ∧
    (min profileABMeet.multiplicity profileC.multiplicity,
      min profileABMeet.seedCap profileC.seedCap,min profileABMeet.slopeCap profileC.slopeCap)=
      (profileFinalMeet.multiplicity,profileFinalMeet.seedCap,profileFinalMeet.slopeCap) := by decide
theorem profile_gates :
    profileA.characteristicCap<prime ∧ profileB.characteristicCap<prime ∧
    profileC.characteristicCap<prime ∧
    profileA.weightedCap+profileA.slopeCap≤w*(profileA.yCap+1) ∧
    profileB.weightedCap+profileB.slopeCap≤w*(profileB.yCap+1) ∧
    profileC.weightedCap+profileC.slopeCap≤w*(profileC.yCap+1) ∧
    profileA.multiplicity-1+profileA.slopeCap≤profileA.yCap ∧
    profileB.multiplicity-1+profileB.slopeCap≤profileB.yCap ∧
    profileC.multiplicity-1+profileC.slopeCap≤profileC.yCap := by decide
theorem profile_small_gates :
    (2*profileA.slopeCap-1)*profileA.seedCap<prime ∧ profileA.slopeCap<prime ∧
    (2*profileB.slopeCap-1)*profileB.seedCap<prime ∧ profileB.slopeCap<prime ∧
    (2*profileC.slopeCap-1)*profileC.seedCap<prime ∧ profileC.slopeCap<prime := by decide

def fixedFlag : FlagDegree := surfaceFlag 1150 43 9
def direction : FlagDegree := directionFlag 1150 43 9
def centre : FlagDegree := centreFlag 1150 43 9
def q : ℕ := quad 1150 43 9 fixedFlag
def qeff : ℕ := ContactMovingPositiveLedger6719Research.qeff 1150 43 9 fixedFlag
def ell : ℕ := ContactMovingPositiveLedger6719Research.ell 1150 43 9 fixedFlag
def unit : ℕ := ContactMovingPositiveLedger6719Research.unit 1150 43 9 fixedFlag
def zlin : ℕ := zSlope 1150 43 9 fixedFlag
def zunit : ℕ := flagMixed fixedFlag unitYZFlag unitZFlag
def E : ℕ := (n*gap*w+agreements-1)/agreements
def U : ℕ := n-w

def degreeCost : ℕ := qeff*E+(q+ell)*U+(errors+1)*gap*(zlin+ell)
def unitCost : ℕ := (q+ell)*E+unit*U+
  (errors+1)*gap*(zlin+zunit+ell+flagMixed fixedFlag unitYZFlag unitYZFlag)
def fixedProperTailCost : ℕ := ((w+1)*degreeCost+unitCost)/gap+1

def identityFlag : FlagDegree := centre+(w+1) • direction
def firstTailFlag : FlagDegree := centre+w • direction
def identityZDegree : ℕ := flagMixed fixedFlag identityFlag unitZFlag
def identityYZDegree : ℕ := flagMixed fixedFlag identityFlag unitYZFlag
def fixedIdentityYZCost : ℕ := U*(errors+1)*(identityZDegree+identityYZDegree)/gap+1
def fixedRegularCost : ℕ := fixedProperTailCost+fixedIdentityYZCost

def singularY (P : Profile) : ℕ := (P.characteristicCap-1)/w
def singularZ (P : Profile) : ℕ := (2*P.slopeCap-1)*P.seedCap
def singularNumerator (P : Profile) : ℕ :=
  let y:=singularY P; let z:=singularZ P
  U*((1+2*w*y)*z+w*(2*y*z)+(2*w*z+1)*y)+(errors+1)*gap*y+2*z*z*gap
def singularCeiling (P : Profile) : ℕ := singularNumerator P/gap+1
def residualMixed (P Q : Profile) : Fin 3 → ℕ :=
  ![P.slopeCap*Q.seedCap+P.seedCap*Q.slopeCap,
    P.yCap*Q.seedCap+P.seedCap*Q.yCap,P.yCap*Q.slopeCap+P.slopeCap*Q.yCap]
def residualNumerator (P Q : Profile) : ℕ :=
  let c:=residualMixed P Q
  U*(c 0*(1+2*w*max P.yCap Q.yCap)+c 1*(w*(2*max P.slopeCap Q.slopeCap-1))+
    c 2*(2*w*max P.seedCap Q.seedCap+1))+(errors+1)*gap*c 2
def fixedSingularCost : ℕ := singularCeiling profileFinalMeet
def firstResidualRegularCost : ℕ := residualNumerator profileA profileB/gap
def firstResidualSingularCeiling : ℕ := singularCeiling profileB
def secondResidualRegularCost : ℕ := residualNumerator profileABMeet profileC/gap
def secondResidualSingularCeiling : ℕ := singularCeiling profileABMeet
def fixedCost : ℕ := fixedRegularCost+fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost+firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost+secondResidualSingularCeiling
def totalCost : ℕ := fixedCost+firstResidualCeiling+secondResidualCeiling

theorem fixed_ledger_values :
    fixedFlag=⟨1150,44,11⟩ ∧ direction=⟨2300,87,21⟩ ∧
    q=14732934 ∧ qeff=10923492 ∧ ell=51562 ∧ unit=14836069 ∧
    zlin=2112 ∧ zunit=11 ∧ E=9624450283 ∧ U=131073 ∧
    degreeCost=105353736004668444 ∧ unitCost=142513873647988405 ∧
    fixedProperTailCost=270766027440736281 ∧ identityZDegree=276826187 ∧
    identityYZDegree=6758386037 ∧ fixedIdentityYZCost=1447810727420080 ∧
    fixedRegularCost=272213838168156361 := by decide
theorem qeff_positive_parts :
    flagMixed fixedFlag direction (normalFlag 1150 43 9)=6955726 ∧
    flagMixed fixedFlag (fiberFlag 1150 43 9) fixedFlag=3967766 ∧
    qeff=6955726+3967766 := by decide
theorem residual_values :
    residualMixed profileA profileB=![549127,2481314,2580] ∧
    residualMixed profileABMeet profileC=![318269,1668177,1301] ∧
    residualNumerator profileA profileB=6020621374799599221 ∧
    residualNumerator profileABMeet profileC=2528055970245169689 := by decide
theorem six_cells_exact :
    fixedRegularCost=272213838168156361 ∧ fixedSingularCost=59637005127661 ∧
    firstResidualRegularCost=118051399505874 ∧ firstResidualSingularCeiling=582880209987137 ∧
    secondResidualRegularCost=49569724906768 ∧ secondResidualSingularCeiling=62654593239340 := by decide
theorem total_and_slack_exact : totalCost=273086631100923141 ∧
    mcaBudget-totalCost=1894096010471946 ∧ totalCost<mcaBudget := by decide
theorem residual_characteristic_gates :
    singularY profileB=5092 ∧ singularZ profileB=56635 ∧
    2*singularY profileB*singularZ profileB<prime ∧
    singularY profileABMeet=1225 ∧ singularZ profileABMeet=25305 ∧
    2*singularY profileABMeet*singularZ profileABMeet<prime ∧
    singularY profileFinalMeet=1166 ∧ singularZ profileFinalMeet=25305 ∧
    2*singularY profileFinalMeet*singularZ profileFinalMeet<prime ∧
    (1+w*(direction.yz+direction.all))*fixedFlag.all+
      (fixedFlag.yz+fixedFlag.all)*(w*direction.all)<prime := by decide
theorem first_tail_characteristic_gates :
    (fixedFlag.yz+fixedFlag.all)*firstTailFlag.all+
      (firstTailFlag.yz+firstTailFlag.all)*fixedFlag.all=307101707 ∧
    (fixedFlag.yz+fixedFlag.all)*firstTailFlag.all+
      (firstTailFlag.yz+firstTailFlag.all)*fixedFlag.all<prime ∧
    (fixedFlag.yz+fixedFlag.all)*identityFlag.all+
      (identityFlag.yz+identityFlag.all)*fixedFlag.all=307104050 ∧
    (fixedFlag.yz+fixedFlag.all)*identityFlag.all+
      (identityFlag.yz+identityFlag.all)*fixedFlag.all<prime ∧
    2*(fixedFlag.zOnly+fixedFlag.yz+fixedFlag.all)*
      ((fiberFlag 1150 43 9).zOnly+(fiberFlag 1150 43 9).yz+(fiberFlag 1150 43 9).all)=2906460 ∧
    2*(fixedFlag.zOnly+fixedFlag.yz+fixedFlag.all)*
      ((fiberFlag 1150 43 9).zOnly+(fiberFlag 1150 43 9).yz+(fiberFlag 1150 43 9).all)<prime := by decide

/-- Arithmetic consumer; construction of these three cell bounds is external. -/
theorem total_lt_mcaBudget (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total=firstResidual+secondResidual+fixed)
    (hfirst : firstResidual<firstResidualCeiling)
    (hsecond : secondResidual<secondResidualCeiling)
    (hfixed : fixed≤fixedCost) : total<mcaBudget := by
  have hsum : firstResidual+secondResidual+fixed<totalCost := by
    calc
      _ < firstResidualCeiling+secondResidual+fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_right hfirst secondResidual) fixed
      _ < firstResidualCeiling+secondResidualCeiling+fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hsecond firstResidualCeiling) fixed
      _ ≤ firstResidualCeiling+secondResidualCeiling+fixedCost :=
        Nat.add_le_add_left hfixed (firstResidualCeiling+secondResidualCeiling)
      _ = totalCost := by unfold totalCost; ring
  calc
    total = _ := hpartition
    _ < totalCost := hsum
    _ < mcaBudget := total_and_slack_exact.2.2

#print axioms interpolation_gates
#print axioms six_cells_exact
#print axioms total_and_slack_exact
#print axioms total_lt_mcaBudget
end ProximityPrize.SubmissionLower.ContactMovingParameters6731Research
