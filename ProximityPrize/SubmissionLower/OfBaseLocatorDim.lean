/-
ofBase-coefficient cut of the 33-dim Ext6 BW kernel.

Not puncture, not N×N det, not kernel *existence* (KernelSurj), not
⟨γ⟩-order vs deg R (BWGammaLift). Genuine MCA error locators at cell
65552 are coefficient-wise `algebraMap` / `ofBase` of a KoalaBear
base-field polynomial. That is an 𝔽_p-linear constraint the Ext6-linear
33-dim kernel does not encode.

Locator space of degree ≤ e:
  𝔽_p-dim ofBase = e+1 = 65553
  𝔽_p-dim Ext6   = 6(e+1) = 393318
  ofBase-codim   = 5(e+1) = 327765
Ext6 kernel is 33-dimensional, hence 198-dimensional over 𝔽_p.
198 ≪ 327765: a generic kernel vector is *not* a base locator.
-/
import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.OfBaseLocatorDim

open Polynomial
open ProximityPrize.Benchmark

/-- Error locator over the KoalaBear base field. -/
noncomputable def baseLocator (D : Finset IRSProfile.Index) :
    Polynomial _root_.KoalaBear.Field :=
  ∏ i ∈ D,
    ((Polynomial.X : Polynomial _root_.KoalaBear.Field) -
      Polynomial.C (IRSProfile.baseNttDomain.node i))

/-- Same locator over the sextic challenge field. -/
noncomputable def extensionLocator (D : Finset IRSProfile.Index) :
    Polynomial IRSProfile.Field :=
  ∏ i ∈ D,
    ((Polynomial.X : Polynomial IRSProfile.Field) -
      Polynomial.C (IRSProfile.domain i))

/-- Actual support locators are coefficient-wise ofBase, not arbitrary Ext6. -/
theorem extensionLocator_eq_map (D : Finset IRSProfile.Index) :
    extensionLocator D =
      (baseLocator D).map
        (algebraMap _root_.KoalaBear.Field IRSProfile.Field) := by
  classical
  rw [extensionLocator, baseLocator, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [IRSProfile.domain, CompPoly.Extension.Ext.algebraMap_eq_ofBase]

/-- Every coefficient of a genuine extension locator is in the image of
    `algebraMap` from the KoalaBear base field (i.e. `ofBase`). -/
theorem coeff_extensionLocator_is_base
    (D : Finset IRSProfile.Index) (n : ℕ) :
    ∃ a : _root_.KoalaBear.Field,
      (extensionLocator D).coeff n =
        algebraMap _root_.KoalaBear.Field IRSProfile.Field a := by
  refine ⟨(baseLocator D).coeff n, ?_⟩
  rw [extensionLocator_eq_map, Polynomial.coeff_map]

def e : ℕ := 65552

/-- 𝔽_p-dimension of degree-≤e locators with ofBase coefficients. -/
theorem base_locator_fp_dim : e + 1 = 65553 := by native_decide

/-- 𝔽_p-dimension of the same space with Ext6 coefficients. -/
theorem ext_locator_fp_dim : (e + 1) * 6 = 393318 := by native_decide

/-- Extra Ext6 locator freedom vs ofBase: 5 coefficients per degree. -/
theorem ofBase_codim : (e + 1) * 5 = 327765 := by native_decide

/-- Rectangular Ext6 kernel, as an 𝔽_p-space. -/
theorem ker_fp_dim : 33 * 6 = 198 := by native_decide

/-- Kernel over 𝔽_p is strictly smaller than ofBase-codimension. -/
theorem ker_lt_ofBase_codim : 33 * 6 < (e + 1) * 5 := by native_decide

/-- Combined interpolant (Q₁ deg≤e ofBase, Q₀ deg≤e+deg Ext6), 𝔽_p count. -/
def q0_cols : ℕ := e + 131072 + 1
theorem q0_cols_val : q0_cols = 196625 := by native_decide
theorem q1_base_plus_q0_ext_fp : (e + 1) + q0_cols * 6 = 1245303 := by native_decide
theorem bw_eqs_fp : 6 * 2 ^ 18 = 1572864 := by native_decide
/-- ofBase-Q₁ + Ext6-Q₀ is overdetermined over 𝔽_p by 327561. -/
theorem ofBase_q1_overdetermined :
    6 * 2 ^ 18 - ((e + 1) + q0_cols * 6) = 327561 := by native_decide
/-- The unconstrained Ext6 system is *underdetermined* by 33. -/
theorem ext6_underdetermined : 262177 - 2 ^ 18 = 33 := by native_decide

end ProximityPrize.SubmissionLower.OfBaseLocatorDim
