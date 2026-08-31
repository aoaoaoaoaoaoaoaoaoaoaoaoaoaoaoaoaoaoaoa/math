# Decimal Setter Singleton-Carrier Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** singleton-current unit-carrier transitions are impossible; multi-to-singleton
unit carriers exist exactly at upper length `m≥β+3`, so encoded reachability is the remaining
singleton obstruction

This audit completes the singleton seam left open by
[`MM-S18`](../SALVAGE.md#mm-s18-length-two-carrier-extinction). It does not settle `M₅(3)`.

## Pole Equation

Write a recursive carrier and one block as

```text
t=N/(10μD),
R=NT₂−10μGV₂D.
```

If the block output equals the following block's pole, exact elimination gives

```text
RT₃=EμG10^mNV₃.                                  (1)
```

Here `m` is the current upper-word length, `T₂` and `T₃` are the current and target traces,
and `V₂,V₃` are their lower codes. The proof assumes only that `E,G,μ,N,D,V₂,V₃` are nonzero
rational decimal units. It is therefore insensitive to signs, rational denominators, and the
emitted body except through the displayed parameters.

## Singleton Current

For `β≥3`, a singleton current trace has shell `(β+1,β)`. In `R`, the trace term `NT₂` is
strictly deeper than the built-in decimal term `10μGV₂D` at both primes. Hence

```text
(ν₂(R),ν₅(R))=(1,1).                              (2)
```

If the target is multi-role, its trace has shell `(1,1)`. Equation (1) then forces `m=2`.
The physical current block is either `D_c`, whose upper spelling has length one, or `D_b`,
whose upper spelling has length `β+2`; neither has length two.

If the target is another singleton, (1) instead requires both

```text
m=1+(β+1),
m=1+β,
```

which is impossible. Thus neither singleton erasure can lead to any later pole from a
decimal-unit carrier.

## Multi To Singleton

For a multi-role current trace and singleton target, equation (1) forces

```text
(ν₂(R),ν₅(R))=(m−β−1,m−β).                        (3)
```

Both summands of `R` have valuation at least one at two, so (3) gives `m≥β+2`. Equality would
give `ν₂(R)=1`. After division by ten, however, the two summands are two-adic units. Their
difference cannot remain a two-adic unit, by the cancellation law formalized in `MM-S18`.
Therefore

```text
m≥β+3.                                            (4)
```

The bound is sharp for the abstract carrier. Set

```text
K=T₂T₃−EμG10^mV₃,
N=10μGV₂T₃/K,
D=1.                                              (5)
```

When (4) holds, the trace product dominates the deeper scaled term in `K`, so `K` has shell
`(β+2,β+1)`. The numerator defining `N` has the same shell; hence `N` is a decimal unit.
Multiplying (5) by `K` reduces (1) to an identity. Consequently

```text
∃ decimal-unit rational carrier satisfying (1)  ↔  m≥β+3.   (6)
```

## Reset And Reachability Scope

[`MM-S13`](../SALVAGE.md#mm-s13-decimal-first-transfer-extinction) already excludes a first
singleton false pole from both centered resets. The ordinary reset is closed through two
transfers by `MM-S16`; the distinguished reset supplies the initial decimal-unit carrier for
the recursive corridor. Equations (2)--(6) then apply without retaining a reset sign.

The carrier in (5) is an arbitrary rational unit, not a proved encoded suffix residual.
Therefore (6) is not a false pole for the setter and does not refute the construction. It proves
that valuations plus unrestricted rational-carrier algebra are complete on this seam and cannot
exclude the remaining long branch. Any closure must prove that (5) is unreachable from the
distinguished two-`c` entry, derive stronger encoded suffix semantics, or exhibit a reachable
instance.

## Verification

`DecimalSetterDepth.lean` checks the generic target-shell law, both physical singleton-current
extinctions, the lower bound (4), the construction (5), and the equivalence (6). The declarations
are warning-free and use no proof apertures. Their reviewed transitive axiom set is recorded in
`verification/axioms.txt`.

## Artifacts

- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s20-singleton-carrier-classification)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
