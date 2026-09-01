# Complete B-Bearing Rule-Entry Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no b-bearing rightmost-rule block reaches the physical multi-role pole shell from
a lawful two-`c` raw head

## Exceptional Head

Multiply the three residual arms from MM-S56 by `45`. The exceptional all-`D_c` normal form
has normalized leading coefficient `2`, except at `n=2β−1`, where its two terms collide with
coefficient `4`. The rightmost-`b` upper perturbation and rightmost-rule phase perturbation both
have coefficient `2`, independently of earlier markers and of whether zero, one, or at least
two roles precede the rule.

The proof classifies every strict ordering and equal-depth collision. At a minimum depth, the
possible coefficient sums are `2`, `4`, `2+2`, `4+2`, `2+2+2`, or `4+2+2`; none is zero
modulo five. The scaled residual therefore has the minimum displayed depth, which is strictly
shallower than the physical target.

## Regular Head

Let `h` be the final-seven width. MM-S56 forces every regular b-bearing survivor to have a
nonleading rule and erasure-tail width `h`. After multiplication by `81`, both the all-`D_c`
base and phase perturbation have normalized coefficient `2^h`. Their collision has coefficient
`2·2^h`, a five-adic unit. The rightmost-`b` upper perturbation has depth at least `β+2`, hence
is strictly deeper than `h+1` because `h+2≤β`. It cannot alter the collision depth.

## Assembly

`bBearingRightmostRule_rawHead_shell_impossible` invokes the exact S56 position grammar. Its
regular branch calls the `81`-scaled obstruction; its exceptional branch calls the `45`-scaled
three-arm obstruction. These cases exhaust every b-bearing rightmost-rule block followed by an
erasure tail.

The result does not cover all-`c` words, generalized later carriers, or singleton targets. The
all-`c` S56 grammar retains the position-two boundary and the exact regular or exceptional
later-frontier resonances.

## Verification

`MatrixMortality/DecimalSetterRuleCoefficient.lean` contains the normalized-residue predicate,
all pairwise and triple collision cases, exact exceptional and regular coefficient profiles,
both physical branch obstructions, and the grammar-consuming extinction theorem. The narrow
and root builds, Lean language-server diagnostics, namespace lint, selected transitive axiom
checks, forbidden-form scan, and diff check pass without warnings, suppressions, or proof
apertures.

## Artifacts

- [`DecimalSetterRuleCoefficient.lean`](../MatrixMortality/DecimalSetterRuleCoefficient.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s60-complete-b-bearing-rule-entry-extinction)
