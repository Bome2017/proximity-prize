import ProximityPrize.Benchmark.TargetLower

/-!
Sextic / base-field structure of γ, tied to the 33-dimensional BW kernel.

The BW kernel of `KernelSurj.lean` lives over `IRSProfile.Field = KoalaBear.Ext6`
(`𝔽_{p^6}`, `X^6+X^3+1`). The evaluation domain is *not* the full sextic:
it is the size-`2^18` KoalaBear base-field NTT, coefficient-wise `ofBase`
into Ext6. The FRS generator `γ` is a genuine Ext6 element of order `2^21`
(`ToyProblem.Impl.FRS.gamma_exists`), not a base-field unit.

Defense files mixed two primes:
  KoalaBear `2^31-2^24+1 = 2130706433`
  BabyBear  `2^31-2^27+1 = 2013265921`  (BWSyndromeCut.p)
-/

namespace ProximityPrize.SubmissionLower.GammaSextic

open ProximityPrize.Benchmark

/-- Challenge field is the KoalaBear sextic. -/
theorem field_eq_ext6 : IRSProfile.Field = KoalaBear.Ext6 := rfl

/-- `|𝔽| = p^6`. -/
theorem card_field : Fintype.card IRSProfile.Field = KoalaBear.fieldSize ^ 6 :=
  KoalaBear.card_ext6

def koalaP : Nat := 2 ^ 31 - 2 ^ 24 + 1
def babyP : Nat := 2 ^ 31 - 2 ^ 27 + 1

theorem koalaP_eq : koalaP = 2130706433 := by native_decide
theorem babyP_eq : babyP = 2013265921 := by native_decide
theorem koalaP_ne_babyP : koalaP ≠ babyP := by native_decide

/-- Live KoalaBear prime matches `2^31-2^24+1`, not BWSyndromeCut's 2013265921. -/
theorem fieldSize_eq_koalaP : KoalaBear.fieldSize = koalaP := by native_decide

theorem ext6_degree : KoalaBear.ext6Params.d = 6 := rfl

/-- Every domain node is a base-field embedding. -/
theorem domain_ofBase (i : IRSProfile.Index) :
    ∃ a : KoalaBear.Field, IRSProfile.domain i = CompPoly.Extension.Ext.ofBase a :=
  ⟨IRSProfile.baseNttDomain.node i, rfl⟩

/-- Recover the base node as coefficient 0 of the sextic embedding. -/
theorem domain_coeff0 (i : IRSProfile.Index) :
    CompPoly.Extension.Ext.coeff (IRSProfile.domain i) (0 : Fin 6) =
      IRSProfile.baseNttDomain.node i := by
  simp [IRSProfile.domain, CompPoly.Extension.Ext.coeff_ofBase]

/-- `2^21` divides the Ext6 unit-group order, so an element of that order exists. -/
theorem two_pow_21_dvd_ext6_units :
    2 ^ 21 ∣ koalaP ^ 6 - 1 := by
  native_decide

/-- Base-field 2-adicity: `2^24 | p-1`, hence `2^21 | p-1` already in 𝔽_pˣ. -/
theorem two_pow_21_dvd_base_units :
    2 ^ 21 ∣ koalaP - 1 := by
  native_decide

/-- Cell-65552 column excess (KernelSurj): 33 Ext6-linear degrees of freedom. -/
theorem ker_ext6_dim_num : 262177 - 262144 = 33 := by decide

/-- Those 33 Ext6 dimensions are 198 base-field dimensions. -/
theorem ker_base_dim_num : 33 * 6 = 198 := by decide

end ProximityPrize.SubmissionLower.GammaSextic
