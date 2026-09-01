# Exact Decimal Rule-Resonance Grammar Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** exact five-depths replace the remaining distinguished raw-entry rule language by a
finite positional resonance grammar

## Comparison Frontier

For an all-`D_c` word of role width `n`, a regular two-`c` raw head with final-seven width `h`
has residual five-depth `min(n,h+1)`. The exceptional head `h=β−1` has depth
`min(n,2β−1)`. These are exact valuations. The proofs combine the existing raw-residual normal
forms with matching lower divisibility and next-power nondivisibility.

## Three-Term Cut

For a `b`-bearing block, factor both the rightmost rule and rightmost `b`. The physical residual
is the sum of:

```text
the all-D_c comparison residual,
the upper marker perturbation at depth r+β+2,
the phase perturbation at depth s+2 for a leading rule and s+1 otherwise.
```

Here `r` is the all-`c` tail after the rightmost `b`, and `s` is the erasure tail after the
rightmost rule. The marker coefficient remains a five-adic unit despite arbitrary earlier
markers. The physical target is deeper than the phase term, so the minimum of the three input
depths must be repeated. Lean checks the repeated-minimum condition, not merely pairwise
equality.

## Solved Grammar

At a regular head, the marker depth lies strictly above the comparison frontier. The only
minimum resonance is therefore

```text
the rightmost rule is not leading, and s=h.
```

At the exceptional head, three arms remain: `s=2β−2` with the marker no shallower; base-marker
equality below the phase depth; or marker-phase equality below the base depth. Without a `b`
term, a rule lies either in position two or has tail width `h` in the regular case and `2β−2`
in the exceptional case. The leading all-`c` rule family was already excluded by MM-S54.

## Boundary

The classifier does not assert cancellation on an equal-depth arm. The live work is to compare
normalized coefficients on the exceptional arms and to resolve the all-`c` position-two
boundary using its extra two-adic divisibility. Generalized carriers and singleton targets are
outside this raw-entry theorem.

## Verification

`MatrixMortality/DecimalSetterRuleResonance.lean` contains the exact comparison valuations,
rightmost-`b` perturbation valuation, repeated-minimum theorem, arithmetic grammar collapse,
and physical all-`c` and `b`-bearing classifiers. The narrow and root builds, Lean
language-server diagnostics, namespace lint, selected transitive axiom checks, forbidden-form
scan, and diff check pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterRuleResonance.lean`](../MatrixMortality/DecimalSetterRuleResonance.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s56-exact-rule-resonance-grammar)
