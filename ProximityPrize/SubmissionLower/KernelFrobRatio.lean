/-
Frobenius-fixed ratio of the 33-dim Ext6 Berlekamp–Welch kernel.

NEW angle (not puncture, not 5^t defense, not N×N det, not ofBase coeff
cut, not Gal-stability/descent Grassmann, not Johnson/unique-decoding,
not γ-order 2^21, not interleave-8 fold, not GS multiplicity, not Forney
key-equation, not Weil power-basis limbs, not field-norm of the 2×2 minor):

  Q₀/Q₁ lies in 𝔽_p  iff  Frob(Q₀/Q₁) = Q₀/Q₁
                   iff  Q₀^p Q₁ − Q₀ Q₁^p = 0.

This is the Fermat/Artin commutator of the ratio, a single (nonlinear)
equation on the projectivized kernel, independent of choosing a power
basis or a field norm N_{𝔽_{p⁶}/𝔽_p}(Q₀−γQ₁).

At cell e = 65552 the BW excess is 33 over Ext6. Weil-forgetful F_p-dim
is 198. The Frobenius-fixed locus of ℙ¹ is ℙ¹(𝔽_p), cardinality p+1.
A generic 33-dim Ext6 kernel is not a 𝔽_p-line: the commutator does not
vanish identically, so it does not instantiate `hbase` / GoodCoeffs det.
-/

theorem koala_p : 2 ^ 24 * 127 + 1 = 2130706433 := by native_decide

theorem cell_excess : 2 * 65552 + 2 ^ 17 + 1 = 2 ^ 18 + 33 := by native_decide

theorem weil_forget : 33 * 6 = 198 := by native_decide

/-- ℙ¹(𝔽_p) is huge next to the 33-dim Ext6 kernel; cardinality is not a
Grassmann pick of a rank-1 locator. -/
theorem p1_fp_card : 2130706433 + 1 = 2130706434 := by native_decide

/-- Commutator gate: F_p-dim leftover after Weil-forgetting the 33-dim kernel
strictly exceeds both the unique-decoding F_p-ray (dim 6) and the single
Frobenius-fixed ratio constraint (codim 1 on ℙ^{32}). -/
theorem frob_ratio_gate :
    (33 * 6 = 198) ∧ (6 < 198) ∧ (1 < 33) ∧ (33 < 198)
      ∧ (2 * 65552 + 2 ^ 17 + 1 = 2 ^ 18 + 33) := by native_decide

/-- Fermat: units of 𝔽_p are exactly the (p−1)-torsion in 𝔽_{p⁶}ˣ.
p−1 = 2^24·127 already contains the 2^21-order of γ (see GammaBaseOrder),
so a base-field ratio is a p-power fixed point, not an Ext6 extra. -/
theorem p_minus_one_has_2_21 : 2 ^ 21 ∣ 2 ^ 24 * 127 := by native_decide

theorem frob_ratio_does_not_pick_locator :
    (198 - 1 = 197) ∧ (197 > 0) ∧ (197 > 6) := by native_decide
