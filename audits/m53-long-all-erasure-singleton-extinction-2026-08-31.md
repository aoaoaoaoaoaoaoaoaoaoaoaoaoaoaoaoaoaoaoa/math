# Long All-Erasure Singleton Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the swapped-ternary `D_c^(β+1)` first multi-transfer branch is empty

This audit consumes the two all-erasure alternatives left by
[`MM-S44`](../SALVAGE.md#mm-s44-compiler-envelope-rule-bearing-extinction). It removes the long
singleton-target alternative and leaves `D_c²→multi` as the sole expected-shell first
multi-transfer branch.

## Exact Transfer

Put `ρ=3^β`, `μ=2ρ−1`, and `H=5ρ−1`. The literal block `D_c^(β+1)` has

```text
V_m=3ρ−1,       2P_m=9ρ²+ρ−2.                           (1)
```

If the preceding first block has upper power `A` and punctuated swapped upper code `P`, define

```text
q=(μA−P)/P.
```

The complete upper-code cylinder `ρA≤P<2ρA` implies `q<1`. Substitution of (1) into the
centered recurrence gives

```text
Δ=(9ρ²+ρ−2)/(2ρ) − H(3ρ−1)q/((ρ−2)ρ).                  (2)
```

For `ρ≥27`, replacing `q` by its strict upper bound reduces `Δ>12` to positivity of

```text
9ρ³−71ρ²+60ρ+2.
```

After `t=ρ−27`, this polynomial is

```text
9t³+658t²+15909t+127010,
```

so the inequality is strict throughout the compiler range.

## Singleton Targets

The normalized following-pole equation is

```text
C_tΔ+3HμV_t=0.                                          (3)
```

For singleton erasures, `V_t=2`. Substitution of their exact coefficients into (3) gives

```text
D_c:  Δ=6μ/ρ,
D_b:  Δ=6Hμ/(ρB),       B=18ρ²−40ρ+17.                 (4)
```

The first value is below twelve because `μ<2ρ`. For `ρ≥27`, `0<H<B`; combining this with
`μ<2ρ` puts the second value below twelve. Both contradict (2).

## Composed Boundary

`firstMultiTransfer_pole_forces_doubleDeletion` composes the extinction with `MM-S44`. Under
the compiler body envelope and the expected coefficient, lower-code, and pole-shell hypotheses,
every first multi-transfer pole must satisfy

```text
middle = D_c²,       target depth 1.                     (5)
```

Equation (5) is necessary, not existential. Its normalized discrepancy is generally rational;
the integral positive-depth-one fringe classifier cannot be applied until a separate physical
ancestry theorem constructs its digit-code difference and common-suffix witness. The later
[`MM-S51`](../SALVAGE.md#mm-s51-double-deletion-ratio-chamber-extinction) result bypasses that
interface and excludes (5) through the physical target-code ratio.

## Verification

[`SwappedSetterAllErasure.lean`](../MatrixMortality/SwappedSetterAllErasure.lean) proves the exact
all-erasure codes, equation (2), the strict lower bound, both target equations and bounds, and
the composed frontier theorem. [`SwappedSetterCylinder.lean`](../MatrixMortality/SwappedSetterCylinder.lean)
exports the upper cylinder and exact normalized pole equation consumed by the proof. Both modules
are warning-free and contain no proof aperture. `AxiomAudit.lean` lists the three public result
theorems; the canonical snapshot is regenerated after concurrent integration.

## Artifacts

- [`SwappedSetterAllErasure.lean`](../MatrixMortality/SwappedSetterAllErasure.lean)
- [`SwappedSetterCylinder.lean`](../MatrixMortality/SwappedSetterCylinder.lean)
- [`MM-S44`](../SALVAGE.md#mm-s44-compiler-envelope-rule-bearing-extinction)
- [`MM-S50`](../SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
