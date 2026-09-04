# Complete Two-Block Singleton Extinction Audit

**Date:** 2026-09-01
**Target:** both singleton targets over exactly two parser source blocks
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no parser-lawful two-block source reaches a singleton pole for `β≥3`

## Common Root Equation

The two-block classifier fixes any prospective singleton pole over the root `R_c`, with a
multi-role current block of upper length `m≥β+3`. The calibrated root recurrence has the
target-independent equivalence

```text
HitsSquarePole D_ℓ [current,R_c]
  ↔ singletonTrace(ℓ)·(P−V)=7μ·lift·10^m.             (1)
```

No parser law is required for (1). The parser law supplies the preceding root and length
classifier.

## `D_b` Suffix

For `ρ=10^β`, the singleton `D_b` trace is

```text
2ρB,    B=5200ρ²−18398ρ+2443.
```

Equation (1) becomes

```text
2ρB(P−V)=7μ·lift·10^m.                               (2)
```

Set `w=m−β−1`. The exact `(2,5)` shells in (2) give discrepancy depths `(w,w+1)`. Hence
`10^w ∣ P−V`, but `2·10^w ∤ P−V`. Decimal suffix exhaustion identifies the lower spelling with
the final `w` digits of the punctuated upper spelling and factors

```text
P−V=K·10^w.
```

The complementary prefix code `K` has length exactly `2β+2`. Cancelling (2) yields

```text
B·K=35μ·lift.                                        (3)
```

## Size Contradiction

Every lawful prefix digit is at least five, so `K≥50ρ²`. For `ρ≥1000`, direct coefficient and
marker bounds give

```text
B>4000,    μ<10ρ,    0<lift<502ρ.
```

Thus the left side of (3) exceeds `200000ρ²`, while its right side is below `175700ρ²`. This
excludes `D_b`. Record `MM-S88` independently excludes `D_c`; the combined Lean theorem cases
on the target letter and closes the full slice.

## Boundary

The body and both physical blocks are arbitrary subject to `BlocksLaw [current,root]`. The
theorem assumes only `β≥3`. It does not apply to a singleton pole with three or more source
blocks, whose older homogeneous ray includes at least one intervening physical block rather than
one root ray.

## Verification

The dedicated modules and root aggregate build without warnings. Namespace lint and Lean LSP
diagnostics are clean. The full axiom audit compiles, and every selected declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`. No proof aperture, external declaration,
unsafe definition, or linter suppression is present.

## Artifacts

- [`DecimalSetterTwoBlockSingleton.lean`](../MatrixMortality/DecimalSetterTwoBlockSingleton.lean)
- [`DecimalSetterRuleCRootSingleton.lean`](../MatrixMortality/DecimalSetterRuleCRootSingleton.lean)
- [`DecimalSetterRootRay.lean`](../MatrixMortality/DecimalSetterRootRay.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s89-complete-two-block-singleton-extinction)
