# Decimal Three-Shape Frontier Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every role shape in the swapped ternary first-multi-transfer frontier is empty under
the analogous decimal carrier hypotheses

## Claim

Let `β≥3`. Assume the exact decimal carrier pole equation

```text
(NT₂−10μGV₂D)T₃=EμG10^mNV₃
```

with decimal-unit `N,D,E,G,μ,V₂,V₃`. The equation is impossible in each of the following cases:

| Current shape | Target shell | Decimal obstruction |
| --- | --- | --- |
| two-`c`, hence `m=2`, multi-role | multi-role | `peeledMultiPole_length_ne_two` |
| `(β+1)`-`c`, hence `m=β+1`, multi-role | singleton | `peeledMultiToSingleton_beta_add_three_le` forces `m≥β+3` |
| singleton `D_b` | singleton | `peeledSingletonToSingleton_impossible` |

The last result is stronger than the transferred shape: it does not require the preceding block
to have two `c` roles.

## Scope

The theorem compares two setter candidates. It does not claim that the ternary three-shape gate
classifies the decimal recurrence. Decimal multi-to-multi transitions of length at least three
and multi-to-singleton transitions of length at least `β+3` remain live. The result prevents the
three short ternary survivors from being mistaken for common residuals of both candidates.

## Verification

`MatrixMortality/DecimalSetterMultitransfer.lean` contains the single consuming theorem
`DecimalSetterDepth.firstMultiTransfer_threeShapeFrontier_impossible`. Its module build,
namespace lint, and transitive axiom audit pass without warnings, suppressions, or proof
apertures.

## Artifacts

- [`DecimalSetterMultitransfer.lean`](../MatrixMortality/DecimalSetterMultitransfer.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s37-decimal-three-shape-frontier-extinction)
