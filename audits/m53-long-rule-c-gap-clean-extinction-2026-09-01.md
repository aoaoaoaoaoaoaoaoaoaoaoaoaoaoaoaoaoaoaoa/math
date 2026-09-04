# Long `R_c` Gap-Clean Extinction Audit

**Date:** 2026-09-01
**Target:** gap-clean ancestry on the long `R_c` three-block singleton branch
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every hypothetical pole on this branch has reduced normalized numerator coprime to
the primitive gap, so no gap-clean descended carrier exists

## Exact Quotient

Let `k` be the intervening block's upper length and let

```text
δ = upperBoundaryCode(next)−lowerBoundaryCode(next).
```

At a long `R_c` pole, `MM-S94` proves shell `(k−1,k−1)` and exact suffix exhaustion. If `H` is
the unmatched peeled-head code, the natural and rational differences agree and

```text
δ=H·10^(k−1).                                        (1)
```

The exact two-block ray above `R_c` has quotient `10^k μ/δ`. Substituting (1) gives

```text
(ray₂/ray₁)/10=μ/H.                                  (2)
```

Lean proves this identity directly from the physical parser codes; no abstract projective
representative is selected.

## Coprimality Obstruction

Let `a/b` be the canonical reduced form of the rational in (2). The rational-reduction theorem
supplies an integer common factor with `μ=common·a`; hence `a∣μ`. The primitive gap `q` is
coprime to `μ`, so it is coprime to `a`.

By the exact ancestry criterion in `MM-S91`, gap-clean integral coordinates with descended
denominator exist if and only if `q∣a`. Since `β≥3` gives `q>1`, divisibility and coprimality
contradict each other. Therefore no such coordinates exist on the long `R_c` pole branch.

## Scope

The result is conditional on an actual singleton pole, multi-role current and intervening
blocks, the long-current inequality, and root `R_c`. It eliminates gap-clean ancestry, not the
pole. The peeled head is already restricted by `MM-S94` to the `cb/cc` chambers, but the proof
uses only its exact suffix factorization and nonzero unit code.

## Verification

The dedicated module and root aggregate build without warnings. Selected namespace lint, full
axiom audit, forbidden-aperture scan, and whitespace checks pass. Every selected theorem depends
only on the reviewed standard axiom set.

## Artifacts

- [`DecimalSetterThreeBlockLongContamination.lean`](../MatrixMortality/DecimalSetterThreeBlockLongContamination.lean)
- [`DecimalSetterThreeBlockSingleton.lean`](../MatrixMortality/DecimalSetterThreeBlockSingleton.lean)
- [`DecimalSetterGapCleanAncestry.lean`](../MatrixMortality/DecimalSetterGapCleanAncestry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s98-long-r_c-gap-clean-ancestry-extinction)
