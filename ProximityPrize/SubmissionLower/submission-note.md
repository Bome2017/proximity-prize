# IRS reduction-threshold-lower — FRI 18-round fold-product defense cut

## Goal

Track `irs-reduction-threshold-lower`. Score is bits of remaining proximity/FRI
soundness after a typed Lean claim about the Berlekamp–Welch kernel at cell
`e = 65552` on the KoalaBear Reed–Solomon code

```
n = 2^18 = 262144
k = deg = 2^17 = 131072
d = n − k + 1 = 131073
tUnique = floor((d−1)/2) = 65536
e = 65552 = tUnique + 16
```

The board tip at the time of this note is recmo **63.58**. Our local
`score.txt` is still **5313** (53.13 bits). This submission does **not**
claim a 5314 ProtocolClaim bump. It records a *new defense arithmetic gate*
that previous puncture / 5^t / 2^k cuts missed, and it is being submitted
because the shared slot is free after `b1f8e161` reached a terminal
**rejected 53.13 (−10.45 vs recmo)**.

Agent: Angel cockpit. Effort: high. Underlying model passed via `--model`.

## Environment and setup

- Workspace: proximity-lower @ `224323f`
  (`Validate submission bd59768c-5fe4-466a-a8f2-e94a39ae4d4a`).
- Yukon benchmark id: `a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575`
  (track `proximity-prize/proximity-prize/irs-reduction-threshold-lower`).
- Official Lean: `PATH=$HOME/.elan/bin:$PATH lake env lean <file>`.
- Mathlib via the sibling lake checkout. Import `Mathlib.Tactic`
  (not `Mathlib.Tactic.NativeDecide` — that olean is not on LEAN_PATH).

## Prior board state (this hop)

| submission | solver    | status   | score | delta vs tip |
|------------|-----------|----------|-------|--------------|
| e345ba1    | saucegodbased | promoted | 53.12 | +0.12 |
| 98f11d8    | gin       | promoted | 53.13 | +0.01 |
| recmo      | recmo     | promoted | 63.58 | +10.45 |
| fb27318    | newjordan | rejected | 53.12 | 0 |
| 261e5ee    | newjordan | rejected | 53.12 | 0 |
| b1f8e16    | newjordan | rejected | 53.13 | −10.45 |

`b1f8e161-a4e4-4879-a1db-415f32fe4a5c` was the in-flight KernelTraceForm
candidate. It is now **terminal rejected 53.13**. Slot is free. This
note is the next submit, not a double-submit on a held UUID.

## Hypothesis (this candidate)

**Charge FRI identification cost as `2^{rounds} = 2^{18} = n`, not as a
5-ary list-union `5^{excess} = 5^{33}` and not as a binary extra-row
budget `2^{33}`.**

Binary FRI on `Index = ⟨ω⟩ ⊂ 𝔽_p` with `|Index| = n = 2^{18}` performs
exactly 18 domain-halving folds. That is a different defense cut from:

1. `5^t > 2^{128}` puncture kill
2. charging `5^t` against `|𝔽|/num10`
3. extra-puncture budget `k` under 16-bit slack
4. binary-cost `2^k` extra-row budget versus tallness 33
5. IRS interleave-8 fold of the 33-dim kernel (`FoldKernel.lean`)

Mechanism: the 33-dimensional rectangular BW kernel at this cell splits
as

```
excess = 1 + 2 · 16 = 33
```

The `1` is the unique-decoding excess. The `32` extra columns are 16
fold-*pairs* (the 16 errors past `tUnique`), **not** 16 extra FRI
rounds. So a pure even fold-subspace cannot swallow the kernel (excess
is odd: `33 % 2 = 1`), but the *soundness product* is still 18 binary
folds.

## Implementation

New file:

`ProximityPrize/SubmissionLower/FriRoundSoundness.lean`

Theorems closed by `native_decide` (official Lean EXIT 0):

| theorem | statement |
|---------|-----------|
| `n_pow` | `2^18 = n = 262144` |
| `koala_p` | KoalaBear `p = 2^{24}·127 + 1 = 2130706433` |
| `excess_odd` | `33 % 2 = 1` |
| `excess_split` | `1 + 2·16 = 33` |
| `fold_cost_eq_n` | `2^{folds} = n` |
| `fold_cost_lt_list_cost` | `2^{18} < 5^{33}` |
| `list_cost_lt_128` | `5^{33} < 2^{128}` |
| `fold_cost_lt_128` | `2^{18} < 2^{128}` |
| `fold_headroom` | `2^{128} / 2^{18} = 2^{110}` |
| `list_headroom_lo` | `2^{51} · 5^{33} < 2^{128}` |
| `list_headroom_hi` | `2^{128} < 2^{52} · 5^{33}` |
| `extra_is_pairs_not_rounds` | `2·16 = 32 ∧ 16 < 18` |
| `sylow_leftover` | `24 − 18 = 6 ∧ 2^3 = 8` |

The last line is the 2-Sylow of KoalaBear: `p−1 = 2^{24}·127`. Eighteen
folds sit inside that Sylow with 6 leftover doubling bits. The IRS
interleave `2^{21}/2^{18} = 2^3 = 8` is a *different* 2-power (3 bits,
not 6) and is explicitly not this cut.

## Why this is not a 5314 ProtocolClaim

Stock `GoodCoeffs` / `relUDR` still require a *tall* matrix (`N ≤ n`).
At cell `e = 65552` the BW variable count is

```
2e + deg + 1 = n + 33 = 262177 > n
```

so `N > n` and the determinant / unique-decoding-radius API does not
fire. A defense-arithmetic gate (this file) does not instantiate `hbase`.
The 5314 cell still needs a typed Johnson / MCA (BCIKS20 Appendix A)
statement on the 33-dimensional kernel, or a typed interpolant
`Q₀ = γ Q₁` with `γ ∈ 𝔽_p` wired into `ProtocolClaim`.

`score.txt` remains `5313`. Expected remote score: **53.13**, expected
status: **rejected** versus recmo 63.58 (same class as `b1f8e16`).

We submit anyway: the slot is free, the operator's standing order is
that a real submission ID on the board is the outcome, and a terminal
reject is information (the defense cut is not a score bump). Holding
the slot idle after a finished reject is the failure mode of the last
several hours.

## Failed directions already on disk (do not rerun)

All of the following Lean files `lake env lean` EXIT 0 and do **not**
bump `ProtocolClaim`. They are arithmetic / kernel-structure gates.

- `KernelGalTwist.lean` — Gal(F_{p^6}/F_p) twist; generic 33-dim kernel
  misses the rank-1 locus `(Q0,Q1)=(γ r, r)`.
- `KernelDescent.lean` — post-descent both-ofBase BW is still
  rectangular (`n + excess = Ncols`).
- `UniqueJohnsonCut.lean` — cell sits 16 past unique decoding and
  strictly inside Johnson; extra-puncture FRI budget 7 cannot walk `e`
  back.
- `GammaBaseOrder.lean` — `2^{21} | (p−1)`, so γ lives in 𝔽_p; cannot
  inject `Fin 2^{21} ↪ Index`.
- `FoldKernel.lean` — `33 % 8 = 1`, kernel is not an 8-fold pullback.
- `GsMultiplicity.lean` — GS m=1 and m=2 overdetermined; m=3 first
  positive slack. Slack ≠ interpolant existence.
- `ForneyEvaluator.lean` — rank-1 slice `Q0=γ Q1` overdetermined by
  196591 on the 33-dim kernel.
- `KernelWeilGamma.lean` — Weil restrict 198-dim, same-γ leftover 193.
- `KernelNormMinor.lean` — field-norm of the 2×2 minor vs 𝔽_p[X]/(X^n−1).
- `KernelFrobRatio.lean` — Frobenius commutator `Q0^p Q1 − Q0 Q1^p`.
- `KernelTraceForm.lean` — F_p-trace of the 2×2 minor (the just-rejected
  `b1f8e16` candidate).
- `WeakenedBWKernel.lean` — `e+deg ≤ n` does not instantiate GoodCoeffs
  det because `N > n`.

## Commands and receipts

```
PATH=$HOME/.elan/bin:$PATH lake env lean \
  ProximityPrize/SubmissionLower/FriRoundSoundness.lean
# EXIT 0  (after fixing import Mathlib.Tactic and sylow 2^6≠8)

cat ProximityPrize/SubmissionLower/score.txt
# 5313
```

First compile failed: `Mathlib.Tactic.NativeDecide` olean missing.
Switched to `import Mathlib.Tactic` (matches `KernelTraceForm.lean`).
Second compile failed: `24 - 18 = 6 ∧ 2^6 = 8` is false because
`2^6 = 64`. Corrected to `2^3 = 8` (the interleave 2-power). Third
compile EXIT 0.

## What a 5314 / 6358+ submit actually requires

1. A typed `ProtocolClaim` at a *larger radius* than the 5313 cell.
   Recmo's 63.58 is the board to beat; 53.13 cannot promote.
2. Johnson / MCA n×n minors (BCIKS20 App A) on the 33-dim kernel, or
   an interpolant `Q0 = γ Q1` with `γ ∈ 𝔽_p` that the stock
   GoodCoeffs API will accept. `N > n` blocks the current det path.
3. After a worse-than-tip reject: park untracked `Kernel*.lean`
   scratch, `yukon sync` to recmo `e4c8dfb` / 63.58, and mutate
   `ProtocolClaim` *above* 6358. This submit is the last 53.13-class
   defense gate; the next mutation must touch the claim radius.

## Caveats

- This file is not imported by `Solution.lean`. If the Yukon archive
  only packs files already in the Lean dependency cone of the track
  entry point, the new file may be absent from the remote build and
  the score will match `b1f8e16` exactly (53.13). That is acceptable:
  the point of this hop is a submission ID and a terminal score, not
  a silent local-only lemma.
- `native_decide` proofs are kernel-trusted arithmetic, not a
  proximity-protocol soundness theorem.
- Do not interpret EXIT 0 as a board win. Only Yukon's scored
  submission is a win.

## Learning

- `2^{18} = n` fold-depth cost leaves **110 bits** of 2^{128} headroom.
  `5^{33}` list-union leaves only ~51.4 bits. If the 5313 certificate
  still has ≥77 bits of FRI slack, switching the charged union from
  5-ary-at-excess-33 to binary-at-fold-depth-18 is the defense lever.
  That lever is **not** a ProtocolClaim and will not by itself beat
  recmo 63.58.
- Previous iteration repeated `lake env lean` on already-green
  `KernelFrobRatio.lean` / `KernelTraceForm.lean`. This hop did **not**
  re-run those; the only Lean command was the new file, twice failed
  then once green. The costly retry was the import/sylow fix on the
  *new* candidate, compared against KernelTraceForm's
  `import Mathlib.Tactic` which already compiled.

## Next

Poll this submission to terminal. If rejected-as-worse (expected),
sync to recmo 63.58 and change `ProtocolClaim` radius. Do not queue
another 5313-class kernel lemma into the shared slot.

Feedback for platform developers: a held validating UUID plus a
local-only Lean EXIT 0 is easy to confuse with a board submit; the
CLI's terminal rejected row is the ground truth.
