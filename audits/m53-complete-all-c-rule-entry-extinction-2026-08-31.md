# Complete All-C Rule-Entry Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no all-`c` rightmost-rule block reaches the physical multi-role pole shell from a
lawful two-`c` raw head

## Regular Frontier

Let `h` be the final-seven width of a regular raw head. The S56/S62 grammar forces a later rule
to have erasure-tail width `h` and at least two preceding roles. Multiplication by `81` exposes
normalized leading residue `2^h` on both the all-erasure companion and the phase perturbation.
Their sum has residue `2·2^h`, which is nonzero modulo five. The rule residual therefore has
exact five-depth `h+1`, while the physical target is at least `h+2`.

## Exceptional Frontier

At the exceptional raw head, the forced erasure-tail width is `2β−2`. Multiplication by `45`
places the companion and phase perturbation at common depth `2β`. The companion coefficient is
`2` or `4`; the phase coefficient is `2`. Their sum is `4` or `6` modulo five and cannot
cancel. Because at least two roles precede the rule, the scaled physical target has depth at
least `2β+1`.

## Assembly

`laterAllCRightmostRule_rawHead_shell_impossible` proves both coefficient obstructions.
`allCRightmostRule_rawHead_shell_impossible` invokes the exact S62 grammar, rejects leading and
position-two rules through the existing physical theorems, and dispatches every later rule.

The result covers the complete all-`c` rightmost-rule branch. B-bearing rules, generalized
later carriers, and singleton targets remain outside this theorem.

## Verification

`MatrixMortality/DecimalSetterAllCRule.lean` contains the two later-frontier collision proof
and its complete all-`c` assembly. The narrow and root builds, namespace lint, selected
transitive axiom checks, forbidden-form scan, and diff check pass without warnings,
suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterAllCRule.lean`](../MatrixMortality/DecimalSetterAllCRule.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s65-complete-all-c-rule-entry-extinction)
