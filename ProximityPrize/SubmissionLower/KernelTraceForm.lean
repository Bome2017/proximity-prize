/-
Trace form of the 2×2 Berlekamp–Welch minor, not Weil restriction,
field-norm, or Frobenius commutator.

At cell e = 65552 the Ext6 kernel is 33-dimensional. Weil restriction
gives an F_p-space of dimension 198. The field trace

  Tr_{𝔽_{p⁶}/𝔽_p}(Q₀ − γ Q₁) ∈ 𝔽_p[X]

is a single F_p-linear form (ker Tr has F_p-dim 5 per scalar). Imposing
one trace-zero condition therefore leaves a 197-dimensional F_p-space.

Requiring the *whole* trace polynomial of degree < e+deg+1 to vanish
imposes 196625 coefficient conditions on a 198-dimensional space, so
that gate is overdetermined by 196427. Arithmetic overdetermination
does not instantiate `hbase` / GoodCoeffs det (still N > n).
-/

import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.KernelTraceForm

/-- Evaluation support size `2^18`. -/
def n : Nat := 262144

/-- Cell radius (errors) sitting 16 past unique decoding. -/
def e : Nat := 65552

/-- RS degree bound `2^17`. -/
def deg : Nat := 131072

/-- Rectangular BW excess at this cell. -/
def excess : Nat := 33

/-- `[𝔽_{p⁶} : 𝔽_p]`. -/
def extDegree : Nat := 6

/-- Weil restriction of the Ext6 kernel. -/
def weilDim : Nat := excess * extDegree

/-- One F_p-linear trace form (not 5 same-γ diagonal equations). -/
def traceCodim : Nat := 1

/-- Leftover F_p-dimension after one trace-zero condition. -/
def leftover : Nat := weilDim - traceCodim

/-- Coefficient count of Tr(Q₀ − γ Q₁) as a polynomial of deg < e+deg+1. -/
def locatorDegBound : Nat := e + deg + 1

/-- Overdetermination of vanishing of the whole trace polynomial. -/
def overdet : Nat := locatorDegBound - weilDim

/-- `dim_{𝔽_p} ker Tr = 5`. -/
def traceKernelDim : Nat := extDegree - 1

/--
Three-way gate:
* Weil dim is 198
* one trace form leaves 197
* whole-polynomial trace vanishing is overdetermined by 196427
* ker Tr is 5-dimensional and strictly smaller than the restricted kernel
-/
theorem trace_form_gate :
    weilDim = 198 ∧
    leftover = 197 ∧
    locatorDegBound = 196625 ∧
    weilDim < locatorDegBound ∧
    overdet = 196427 ∧
    traceKernelDim = 5 ∧
    traceKernelDim < weilDim ∧
    leftover < locatorDegBound ∧
    n = 262144 ∧
    e = 65552 := by
  native_decide

end ProximityPrize.SubmissionLower.KernelTraceForm
