/-
Weil restriction / power-basis cut of the 33-dimensional Ext6
Berlekamp–Welch kernel at cell e = 65552, with γ ∈ 𝔽_p.

This is *not* puncture, defense, N×N det, ofBase-locator image,
Galois-descent, Johnson interior, γ-order 2^21, IRS fold,
Guruswami–Sudan multiplicity, or the Forney key-equation section.

Mechanism.  Ext6 = 𝔽_p[ω]/(irreducible sextic), so every pair
(Q₀, Q₁) ∈ Ext6[X]² expands uniquely as

  Qᵢ = Σ_{j=0}^{5} Qᵢⱼ ωʲ ,   Qᵢⱼ ∈ 𝔽_p[X].

The 33-dimensional Ext6 kernel therefore Weil-restricts to a
198-dimensional 𝔽_p-space (finding: 33·6 = 198), which is
*exactly* six copies of a 33-dimensional base-field kernel
rather than six independent kernels.

The rank-1 condition Q₀ = γ Q₁ with the *same* γ ∈ 𝔽_p is the
diagonal constraint Q₀ⱼ = γ Q₁ⱼ for all six power-basis limbs.
That is five independent ratio-matching equations on top of one
BW copy: the six limbs must share one KoalaBear scalar, not six
independent Ext6 slopes.

Arithmetic (closed by `decide`):
  excess = 33
  [Ext6:𝔽_p] = 6
  𝔽_p-dim = 198
  ratio-matching corank = 5
  198 − 5 = 193 > 0

So Weil restriction + same-γ coupling does *not* kill the kernel
and does *not* pick the rank-1 ray (γΛ, Λ). Existence of a
power-basis-diagonal interpolant is still a typed ProtocolClaim
(5314), not a Grassmann / dimension count. Do not submit 5313.
-/

namespace ProximityPrize.SubmissionLower.KernelWeilGamma

def n : Nat := 262144
def e : Nat := 65552
def excess : Nat := 33
def extDegree : Nat := 6
def fpKernel : Nat := 198
def ratioMatching : Nat := 5
def afterCoupling : Nat := 193

theorem fp_kernel_dim : excess * extDegree = fpKernel := by decide
theorem six_copies_of_excess : extDegree * excess = fpKernel := by decide
theorem coupling_leaves_positive : fpKernel - ratioMatching = afterCoupling := by decide
theorem coupling_does_not_kill : 0 < afterCoupling := by decide
theorem coupling_lt_fp_kernel : ratioMatching < fpKernel := by decide

/-- Same-γ coupling is 5 equations on 6 limbs; leftover 𝔽_p-dim
    193 still dwarfs the 1-dimensional rank-1 ray. -/
theorem ray_lt_coupled_kernel : 1 < afterCoupling := by decide

/-- Cell sits 16 past unique decoding; Weil restriction does not
    change that overflow (6·16 = 96 extra 𝔽_p degrees of freedom
    on top of 6·1 = 6 unique-decoding 𝔽_p rays). -/
def tUnique : Nat := 65536
def pastUnique : Nat := 16

theorem past_unique : e - tUnique = pastUnique := by decide
theorem fp_past_unique : extDegree * pastUnique = 96 := by decide
theorem fp_unique_rays : extDegree * 1 = 6 := by decide
theorem fp_kernel_from_overflow :
    extDegree * 1 + extDegree * (2 * pastUnique) = fpKernel := by decide

/-- 2-sided BW overflow (1+2·16=33 Ext6, 6+192=198 𝔽_p) is strictly
    larger than a 6-fold unique-decoding ray (dim 6). Weil restriction
    therefore does not collapse the kernel onto (γΛ, Λ). -/
theorem unique_ray_lt_fp_kernel : extDegree < fpKernel := by decide

end ProximityPrize.SubmissionLower.KernelWeilGamma
