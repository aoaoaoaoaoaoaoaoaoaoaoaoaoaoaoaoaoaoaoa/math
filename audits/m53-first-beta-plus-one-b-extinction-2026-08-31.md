# First-β+1-Position D_b Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** a sole `D_b` in any of the first `β+1` all-erasure positions cannot carry a lawful
two-`c` raw head to another multi-role pole

## Baseline Depth

For an all-`D_c` block of role width `n≥1`, write `R_c` for the raw-head carrier residual. Lean
checks

```text
5^(n+1) ∤ R_c.                                (1)
```

The proof has two independent branches. A regular raw head has terminal run
`1≤s≤β−2`; its three-term decomposition selects a five-adic unit at exponent `min(n,s+1)`.
The exceptional raw head has `s=β−1`; its two-term decomposition resolves the separate cases
`n+1<2β`, `n+1=2β`, and `2β<n+1`. No conclusion about the exceptional head is imported from the
regular formula.

## Positioned Perturbation

Insert one `D_b` after `a` leading `D_c` roles and before `t` trailing `D_c` roles. The total
role count is `n=a+t+1`. The changed and all-`D_c` punctuated upper words share their final
`t+β+2` decimal digits, giving

```text
10^(t+β+2) ∣ P_b−P_c.                         (2)
```

Both lower words are exactly `0^n`. If `a≤β`, then `n+1≤t+β+2`; hence (2) makes the residual
perturbation divisible by `5^(n+1)`. Equation (1) survives, contradicting the five-adic depth
`n+β` required by a following multi-role pole. In one-indexed language, positions
`1,…,β+1` are excluded.

When `n=3φ(|2·10^β−7|)`, the unchanged lower code contains the full primitive gap. The support
saturator therefore gains no escape from any such early `D_b` placement.

## Boundary

The theorem has exactly one `D_b`, begins at the distinguished raw head, and targets another
multi-role pole. It does not decide positions after `β+1`, multiple marker insertions,
rule-bearing phase words, singleton targets, or generalized product residuals.

## Verification

`MatrixMortality/DecimalSetterFiveDepth.lean` checks (1) with separate regular and exceptional
theorems. `MatrixMortality/DecimalSetterPositioned.lean` checks (2), the lower identity, the
full-gap specialization, and `positionedBErase_rawHead_shell_impossible`. Narrow builds, Lean
language-server diagnostics, namespace lint, and selected transitive axiom snapshots pass
without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterFiveDepth.lean`](../MatrixMortality/DecimalSetterFiveDepth.lean)
- [`DecimalSetterPositioned.lean`](../MatrixMortality/DecimalSetterPositioned.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s40-first-beta-plus-one-position-d_b-extinction)
