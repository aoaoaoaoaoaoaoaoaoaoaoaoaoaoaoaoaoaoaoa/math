# Second-Position D_b Support-Saturator Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no all-erasure block whose second role is `D_b` takes a lawful two-`c` raw head to
another multi-role pole

## Exact Suffix Depth

Compare the equal-role-count upper words for

```text
D_c D_b D_c^t,       D_c^(t+2).
```

The corresponding punctuated encodings share a terminal word of length `t+β+2`: the final
`t+1` encoded `c` bits and the marker of length `β+1`. Decimal concatenation therefore gives

```text
10^(t+β+2) ∣ P_second-b−P_all-c.              (1)
```

Both lower spellings are exactly `0^(t+2)`. Put `n=t+2`. Equation (1) is divisible by
`5^(n+β)`, so the carrier residuals differ only by a term divisible at the complete multi-role
target depth. The all-`D_c` residual is not divisible by that power for any lawful two-`c` raw
head. The second-position residual therefore cannot have shell `(n+β,n+β)`.

At `t=3φ(|2·10^β−7|)−2`, the common lower code is divisible by the full primitive gap. This
excludes the second-position support-saturating family, not merely an arbitrary nonsaturating
word.

## Boundary

For a `D_b` in position `j`, the visible common upper suffix has depth `n+β+2−j`. It reaches the
required depth `n+β` only for `j≤2`. Thus the present five-adic transfer proves exactly the first
two positions. Position three can change the decisive digit and remains open, as do rule-bearing
words and transitions from later generalized carriers.

## Verification

`MatrixMortality/DecimalSetterFiveDepth.lean` checks the general deep-perturbation transfer.
`MatrixMortality/DecimalSetterAncestry.lean` checks (1), the lower-word identity, full-gap
support, and the composed raw-head obstruction. Narrow module builds, Lean language-server
diagnostics, namespace lint, and selected transitive axiom snapshots pass without warnings,
suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterFiveDepth.lean`](../MatrixMortality/DecimalSetterFiveDepth.lean)
- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s39-second-position-d_b-raw-head-extinction)
