# Complete All-Erasure First-Entry Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every non-singleton all-erasure first block misses the next multi-role pole from a
lawful distinguished two-`c` raw head

## Exhaustion

For a role-letter word `w`, the exact prospective-pole depth is

```text
m(w)=|tagEncode_β(w)|−1=|w|+#_b(w)(β+1)−1.                (1)
```

If `w` contains `b`, MM-S49 excludes it at (1). If `w=c^n` with `n≥3`, MM-S19 excludes it.
Since a multi-role block has `|w|≥2`, only `w=cc` remains.

## Two-Role Boundary

For `w=cc`, the punctuated upper code and all-erasure lower code are both congruent to `77`
modulo `100`. The calibrated trace `T=EP+GV` therefore has exact decimal shell `(1,1)`.
The lawful raw head `H`, marker `μ`, lift `G`, and lower code `V=77` are two-adic units. In

```text
R=HT−10μGV,
```

both summands have two-adic depth one. Their unit quotients are odd, so their difference cannot
remain a two-adic unit after dividing by two. Hence `ν₂(R)>1`, contradicting the physical shell
`(1,1)` required at depth `m(cc)=1`.

## Scope

The result covers all non-singleton blocks consisting only of `D_b` and `D_c`, from the initial
distinguished two-`c` raw head toward a multi-role pole. It does not cover a block containing
`R_b` or `R_c`, a singleton target, or any transition after a generalized carrier.

## Verification

`MatrixMortality/DecimalSetterPositioned.lean` checks the exact depth formula, the two-role
trace shell, the two-adic cancellation, and the exhaustive `b`-membership split. Narrow and
root builds, Lean language-server diagnostics, namespace lint, and selected transitive axiom
checks pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterPositioned.lean`](../MatrixMortality/DecimalSetterPositioned.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s53-complete-all-erasure-first-entry-extinction)
