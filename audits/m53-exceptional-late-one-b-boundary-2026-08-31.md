# Exceptional-Late One-D_b Boundary Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every one-`D_b` all-erasure raw-head shell must combine the exceptional raw head
with a `D_b` after position `β+1`

## Regular Heads

Let `1≤s≤β−2` be the terminal zero-run length of a regular two-`c` raw head. For every
all-`D_c` role width `n≥1`, Lean proves

```text
5^β ∤ R_c.                                    (1)
```

For `n<β`, the stronger width cut `5^(n+1)∤R_c` implies (1). For `β≤n`, the exact decomposition

```text
81R_c = 10^(s+1)K + 10^nA + 10^βB
```

has `K≡3 (mod 5)`. The latter two terms vanish modulo `5^β`; the first has valuation `s+1<β`.

A sole `D_b` after `a` leading and before `t` trailing `D_c` roles changes the upper code by a
multiple of `10^(t+β+2)`, hence of `5^β` for every `a,t`. It cannot change (1). No one-`D_b`
position reaches the next multi-role pole at a regular raw head.

## Exact Survivor

The physical raw-head classifier gives either a regular run `s≤β−2` or the exceptional run
`s=β−1`. The first case is now empty at every position. `MM-S40` independently empties every
position with `a≤β` at either head. Therefore any one-`D_b` shell forces

```text
a>β,
9H = 5·10^(β+2) + 2·10^(β−1) − 7.
```

This is a necessary boundary, not an existence theorem.

## Scope

The result covers one `D_b`, no rule roles, the distinguished two-`c` raw head, and a following
multi-role pole. Exceptional-late words, multiple `D_b` roles, rule-bearing blocks, singleton
targets, and generalized carriers remain open.

## Verification

`MatrixMortality/DecimalSetterFiveDepth.lean` checks (1) and its perturbation transfer.
`MatrixMortality/DecimalSetterPositioned.lean` checks the physical all-position exclusion and
the exact exceptional-late necessary condition. Narrow builds, root build, Lean language-server
diagnostics, namespace lint, and selected transitive axiom snapshots pass without warnings,
suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterFiveDepth.lean`](../MatrixMortality/DecimalSetterFiveDepth.lean)
- [`DecimalSetterPositioned.lean`](../MatrixMortality/DecimalSetterPositioned.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s45-exceptional-late-one-d_b-boundary)
