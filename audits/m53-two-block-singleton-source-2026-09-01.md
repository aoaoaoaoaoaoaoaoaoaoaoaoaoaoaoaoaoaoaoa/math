# Two-Block Singleton-Source Audit

**Date:** 2026-09-01
**Target:** singleton targets over exactly two source blocks in the parsed decimal setter
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every parser-lawful pole in this slice has root exactly `R_c` and a multi-role
current block with at least `β+3` upper digits

## Unit Ancestry

For a homogeneous ray `(x,y)`, unit peeled coordinates satisfy

```text
x·10μD = yN,    shell(N)=shell(D)=(0,0).
```

Since `10` has shell `(1,1)` and `μ` is a unit, division proves the intrinsic equivalence

```text
AdmitsUnitPeeledCarrier(x,y)
  ↔ x≠0 and shell(y/x)=(1,1).
```

Conversely, take `D=1` and `N=10μ/(y/x)`. This is a genuine equivalence, not only a necessary
valuation condition.

A physical root with upper spelling length `m` has first coordinate `H/μ`, a decimal unit, and
second coordinate `10^m`. Its quotient therefore has shell `(m,m)`. Unit peeled ancestry holds
for a root exactly when `m=1`.

## Uncancelled Recurrence

Before choosing peeled coordinates, a current block with trace `T`, lower code `V`, and upper
scale `A` followed by a singleton target of trace `S` obeys

```text
(Tx−lift·Vy)S = gap·μ·lift·A·x·7.                    (1)
```

This follows directly from the parser ray and requires no reachability or unit hypothesis.

For a multi-role erasure current block, `T` has shell `(1,1)`. Over a root, the two terms in the
parentheses have shells `(1,1)` and `(m,m)`. If `m≠1`, unequal-valuation subtraction preserves
shell `(1,1)`. Multiplication by the singleton shell `(β+1,β)` gives depths `(β+2,β+1)`, whereas
the right side of (1) has equal depth. Hence `m=1`. Parser law then leaves exactly `R_c`, and the
unit-carrier length theorem forces `upperLength(current)≥β+3`.

## Singleton Current

When the current block is a singleton, its trace has shell `(β+1,β)`. Compare the equal root
depth `m` with `β`.

- If `m<β`, both residual depths equal `m`; multiplication by `S` leaves a one-step imbalance.
- If `m=β`, the two-adic residual depth is `β`, so the left side has depth `2β+1`, above either
  singleton upper length.
- If `β<m`, the five-adic residual depth is `β`, so the left side has depth `2β`, again above
  either singleton upper length for `β≥3`.

Each case contradicts the equal-depth right side of (1). This extinction is independent of root
spelling and phase.

## Surviving Equation

The complete `BlocksLaw [current,root]` classifier leaves one grammar:

```text
root=R_c,
length(current)≥2,
upperLength(current)≥β+3.
```

This is a necessary shape, not a reachable witness. Using the exact `R_c` calibrations
`9H=lift` and `H−10μ=−gap/9`, a `D_c` target reduces the remaining pole equation to

```text
2·10^β(P−V)=7μ·10^m.
```

That suffix discrepancy is the next arithmetic target.

## Verification

The dedicated module and root aggregate build without warnings. Namespace lint and Lean LSP
diagnostics are clean. The full axiom audit compiles, and every selected declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`. The pre-existing repository-wide linter and
global axiom-snapshot debts recorded in the S85 audit remain outside this module. Forbidden-form
and diff checks pass; no proof aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterRootRay.lean`](../MatrixMortality/DecimalSetterRootRay.lean)
- [`DecimalSetterBridgeRay.lean`](../MatrixMortality/DecimalSetterBridgeRay.lean)
- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s86-two-block-singleton-source-classifier)
