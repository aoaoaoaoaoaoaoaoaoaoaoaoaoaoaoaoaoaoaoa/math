# Leading-`b` Shallow-Root Sign Extinction Audit

**Date:** 2026-08-31
**Target:** arbitrary-length shallow roots whose first role carries `b`
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every leading-`b` root has negative exact-length complement and misses every shallow
target

## Exact Formula

Write `tail` for the complete upper spelling after the first role. A `b`-role emits the long tag
`1·0^β·1`, whose decimal code is `10μ+5`. Expanding the full punctuated boundary inside its exact
ambient length cancels the `10μ` contribution and leaves

```text
Δ = −(5·10^(β+1+|tail|) + code(tail)·10^(β+1) + μ).
```

The derivation is phase-independent because rule and erasure roles with the same tag letter have
identical upper words. No inequality is used in the exact identity.

## Sign Gate

The marker is positive, the power term is positive, and the tail code is nonnegative. Thus the
root complement is strictly negative for every deletion width, rest word, and phase spelling.

The generic sign gate assumes `β>0`, making `gap` and `lift` positive. It derives positivity of
both punctuated upper codes from their exact decimal-unit shells and nonnegativity of the target
lower code from its natural-code representation. Consequently S77's left side is positive and
its right side nonpositive. Equality is impossible.

## Frontier Cut

This theorem removes every shallow source beginning in `R_b` or `D_b`, not only the singleton
`R_b` root of MM-S82. Together with the one-`R_c` terminal normalization, all unresolved
malformed shallow roots begin with `c` and contain at least two roles. The exact length-two
frontier is reduced to letter words `cb` and `cc`; phase of the first role does not affect the
one-block root state.

## Verification

The module and root aggregate build without warnings. Dedicated default lint and Lean LSP
diagnostics are clean. The selected transitive axiom audit contains only the reviewed standard
axioms. Forbidden-form and diff checks pass; no proof aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterMinimumBody.lean`](../MatrixMortality/DecimalSetterMinimumBody.lean)
- [`DecimalSetterBridge.lean`](../MatrixMortality/DecimalSetterBridge.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s83-leading-b-shallow-root-sign-extinction)
