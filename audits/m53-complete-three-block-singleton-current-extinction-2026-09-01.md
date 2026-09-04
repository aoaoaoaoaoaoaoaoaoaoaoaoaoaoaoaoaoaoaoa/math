# Complete Three-Block Singleton-Current Extinction Audit

**Date:** 2026-09-01
**Target:** singleton currents in the lawful three-source decimal singleton frontier
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every lawful three-block singleton pole has a multi-role current block

## Root Chamber

For every physical root, the punctuated upper code is at least five times its trailing decimal
place, while the marker is strictly below the next place. After cancellation this gives

```text
rootRay₂/rootRay₁ < 2.                                (1)
```

One singleton erasure step has exact quotient

```text
A·gap·μ / (singletonTrace−7·lift·rootQuotient).       (2)
```

The denominator is positive under (1). Direct trace bounds for both `D_c` and `D_b` make the
quantity in (2) strictly less than two for every `β≥3`.

## Reverse Chamber

At an actual singleton pole with singleton current, parser nondegeneracy and the positive
coefficient theorem make the older numerator nonzero. Solving the exact recurrence gives

```text
olderQuotient
  = currentTrace/(7·lift) − gap·μ·currentScale/targetTrace.
```

For current `D_c`, the principal term grows as `2·10^β/7` and the correction is below two. For
current `D_b`, the cubic trace dominates the marker-scale correction by a still larger margin.
Lean proves the uniform conclusion `olderQuotient>2`. This contradicts (1)-(2) whenever the
intervening block is singleton.

## Deep Multi Intervening Block

For a multi-role intervening block above a root of upper length at least two, the parsed ray
coordinates have shells `(1,1)` and `(k,k)`. Multiplying the first coordinate by a singleton
current trace gives shells `(β+2,β+1)`; the lower-coordinate term remains `(k,k)`.

For `D_c`, the two-adic pole balance asks the residual to lie below both input depths. For
`D_b`, it first forces `k=2`; the five-adic input depths are then unequal, fixing the residual at
two while the pole requires three. Both are contradictions. A shallow rule-ended root has upper
length one and is exactly `R_c`, where `MM-S94` already excludes both singleton currents.

## Canonical Consequence

Every erasure-ended current is nonempty. Splitting its length into one or at least two and using
the preceding extinctions proves

```text
BlocksLaw [current,next,root] ∧ singleton pole
  ⇒ 2≤length(current).
```

With `next` multi-role, this supplies the current hypothesis of the complete `MM-S94` A/B
classifier automatically.

## Boundary

The theorem assumes `β≥3`, parser law, exactly three source blocks, and a singleton target. It
does not exclude a multi-role current followed by a singleton intervening block. It also does
not eliminate any multi/multi branch retained by the classifier.

## Verification

The dedicated module and root aggregate build without warnings. Selected namespace lint, full
axiom audit, forbidden-aperture scan, and whitespace checks pass. Every selected declaration
depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Artifacts

- [`DecimalSetterThreeBlockSingletonPrefix.lean`](../MatrixMortality/DecimalSetterThreeBlockSingletonPrefix.lean)
- [`DecimalSetterThreeBlockSingletonCurrent.lean`](../MatrixMortality/DecimalSetterThreeBlockSingletonCurrent.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s95-complete-three-block-singleton-current-extinction)
