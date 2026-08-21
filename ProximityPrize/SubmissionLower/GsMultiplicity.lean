/-
Guruswami–Sudan multiplicity interpolation at cell e = 65552.

Not puncture, not N×N det, not ofBase/Gal-descent, not unique-decoding radius,
not γ-order, not IRS fold. This asks whether a multiplicity-m interpolant can
force a linear factor `y − γ` (γ ∈ F_p) on the 33-dimensional BW kernel.

RS[n = 2^18, k = 2^17], agreement n − e = 196592.
A (1, k−1)-weighted interpolant of degree ≤ W exists if N₁(W) exceeds the
Hasse-condition count n · m(m+1)/2. The agreed word is a factor when
m(n − e) > W, so the factor-gate uses W_max = m(n − e) − 1.

N₁(W) = ∑_j (W − j(k−1) + 1)_+  with k−1 = 131071.
-/

namespace ProximityPrize.SubmissionLower.GsMultiplicity

def n : Nat := 262144
def k : Nat := 131072
def e : Nat := 65552
def km1 : Nat := 131071
def excessBW : Nat := 33

theorem n_pow : n = 2 ^ 18 := by native_decide
theorem k_pow : k = 2 ^ 17 := by native_decide
theorem km1_val : km1 = k - 1 := by native_decide
theorem agree : n - e = 196592 := by native_decide

/-- BW coefficient count (e+1) + (e+k) undershoots n by `excessBW`. -/
theorem bw_excess : (e + 1) + (e + k) = n + excessBW := by native_decide

/-- GS Hasse conditions at multiplicity m. -/
def gsCond (m : Nat) : Nat := n * (m * (m + 1) / 2)

theorem gs_m1_cond : gsCond 1 = n := by native_decide
theorem gs_m2_cond : gsCond 2 = 786432 := by native_decide
theorem gs_m3_cond : gsCond 3 = 1572864 := by native_decide

/-! ### m = 1 (Berlekamp–Welch): factor-gate overdetermined -/

-- W_max = (n-e) - 1 = 196591; j ∈ {0,1}
-- N₁ = 196592 + 65521 = 262113 < n = 262144
theorem gs_m1_N1 : 196592 + 65521 = 262113 := by native_decide
theorem gs_m1_term1 : 196592 - 131071 = 65521 := by native_decide
theorem gs_m1_factor_overdetermined : 262113 < 262144 := by native_decide
theorem gs_m1_over_by : 262144 - 262113 = 31 := by native_decide

/-! ### m = 2: still overdetermined (no forced factor) -/

-- W_max = 2(n-e) - 1 = 393183; j ∈ {0,1,2} since 3(k-1)=393213 > 393183
-- N₁ = 393184 + 262113 + 131042 = 786339 < 3n = 786432
theorem gs_m2_W : 2 * 196592 - 1 = 393183 := by native_decide
theorem gs_m2_j3_overflow : 3 * 131071 = 393213 := by native_decide
theorem gs_m2_j3_gt_W : 393213 > 393183 := by native_decide
theorem gs_m2_N1 : 393184 + 262113 + 131042 = 786339 := by native_decide
theorem gs_m2_factor_overdetermined : 786339 < 786432 := by native_decide
theorem gs_m2_over_by : 786432 - 786339 = 93 := by native_decide

/-! ### m = 3: first positive GS slack under the factor gate -/

-- W_max = 3(n-e) - 1 = 589775; j ∈ {0,1,2,3,4}
-- 4(k-1)=524284 ≤ 589775 < 5(k-1)=655355
-- N₁ = 589776+458705+327634+196563+65492 = 1638170
-- conditions = 6n = 1572864
-- slack = 65306 > 0
theorem gs_m3_W : 3 * 196592 - 1 = 589775 := by native_decide
theorem gs_m3_j4 : 4 * 131071 = 524284 := by native_decide
theorem gs_m3_j5 : 5 * 131071 = 655355 := by native_decide
theorem gs_m3_j4_le_W : 524284 ≤ 589775 := by native_decide
theorem gs_m3_j5_gt_W : 655355 > 589775 := by native_decide
theorem gs_m3_terms :
    589776 + 458705 + 327634 + 196563 + 65492 = 1638170 := by native_decide
theorem gs_m3_factor_underdetermined : 1572864 < 1638170 := by native_decide
theorem gs_m3_slack : 1638170 - 1572864 = 65306 := by native_decide

/-- Multiplicity 1 and 2 cannot force `y − γ`; multiplicity 3 is the first
GS factor-gate that is dimensionally feasible. This is arithmetic slack,
not a typed `ProtocolClaim` at radius 5314. -/
theorem gs_factor_gate_starts_at_m3 :
    (262113 < 262144) ∧ (786339 < 786432) ∧ (1572864 < 1638170) := by
  native_decide

end ProximityPrize.SubmissionLower.GsMultiplicity
