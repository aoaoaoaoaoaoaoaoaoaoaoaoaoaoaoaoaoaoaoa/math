# All-C Position-Two Rule Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no all-`c` rightmost-rule block with exactly one preceding role reaches the
physical multi-role pole shell from a lawful two-`c` raw head

## Phase Perturbation

Write the block width as `n=t+2`, where `t` erasures follow the rightmost rule. Replacing the
rule and its preceding role by their erasure phases preserves the all-`c` upper spelling and
produces an all-erasure lower word. The lower-code difference has exact five-depth `t+1=n−1`
and is divisible by `2^(t+3)`. The calibrated lift and raw-head gap are decimal units, so the
residual perturbation retains the exact five-depth and remains divisible by `2^n`.

## Raw-Head Dichotomy

For a regular raw head with final-seven width `h`, the `81`-scaled all-erasure residual has
three depth-separated terms. It is divisible by `2^n` for `n≤h+2`; at `n=h+2`, the leading
coefficient supplies the otherwise missing factor of two. For `h+3≤n`, the residual has exact
five-depth `h+1`, strictly below the target `n−1`.

At the exceptional head, the `45`-scaled two-term normal form is divisible by `2^n` for
`n≤2β`. For `2β<n`, its exact five-depth is `2β−1<n−1`.

In either near regime, adding the phase perturbation makes the rule residual divisible by
`2^n`, contradicting exact two-depth `n−1`. In either deep regime, the shallower all-erasure
five-depth survives the sum, contradicting exact five-depth `n−1`.

## Assembly

`positionTwoAllCRightmostRule_rawHead_shell_impossible` proves the physical boundary theorem.
`allCRightmostRule_rawHead_forces_laterResonance` composes it with the S56 grammar, leaving only
tail width `h` at a regular head and `2β−2` at the exceptional head. Those later-frontier
collisions remain open.

## Verification

`MatrixMortality/DecimalSetterPositionTwo.lean` contains both all-erasure two-divisibility
lemmas, the physical position-two obstruction, and the grammar adapter. The narrow and root
builds, namespace lint, selected transitive axiom checks, forbidden-form scan, and diff check
pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterPositionTwo.lean`](../MatrixMortality/DecimalSetterPositionTwo.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s62-all-c-position-two-rule-extinction)
