# Triple-Free Decimal Bridge Frontier Audit

**Date:** 2026-08-31
**Target:** outer mortality converse for the explicit decimal `5 × 5` setter
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** arbitrary mortality is equivalent to a parsed singleton, shallow-reset, or deep
square-pole frontier; arithmetic extinction and primitive-recursive emission remain open

## Cube Elimination

`bridgeScalar_append_delimiter_cube` proves the exact factorization

```text
B(left · S³ · right) = B(left) B(right).
```

Recursive descent therefore extracts a contiguous cube-free scalar-zero chunk from every
scalar-zero word. A zero matrix word is scalar-zero after applying the fixed terminal row and
first-axis column. Conversely, surrounding any scalar-zero word by delimiter cubes gives a
literal zero matrix word. No nonzero exterior-vector hypothesis is required.

## Parser

Boundary delimiter runs preserve the bridge coefficient. An all-delimiter word has coefficient
one, so every cube-free zero has a data-anchored core. `CoreSpelling` parses that core recursively:

- no delimiter after a data letter selects a rule in the current block;
- one delimiter selects an erasure in the current block;
- two delimiters select a singleton erasure and start the next block.

The parser is exhaustive because a third delimiter is forbidden. Every block except the
rightmost ends in erasure; the rightmost ends in rule.

## Execution

`CoreSpelling.mulVec_firstAxis` proves the exact physical action on the five-state root column.
`bridgeState` evaluates role blocks right to left; `squareReset` is the exact side state produced
by `S²`. The first coordinate of a lone rightmost block is

```text
1 + ratio · code(upper),
```

which is positive. A zero core therefore contains at least two blocks and exposes an
erasure-ended target satisfying

```text
(roleProduct target · squareReset(source))₀ = 0.
```

`CoreSpelling.zero_frontier` partitions the target exactly into a singleton erasure, a
non-singleton over one rightmost block, or a non-singleton over a history of at least two blocks.
`isMortal_iff_exists_parsedZeroFrontier` packages both directions of the outer algebraic
mortality normal form. `mortalityProblem_mortal_iff_exists_parsedZeroFrontier` transports it
through exact rational denominator clearing to the integer `M₅(3)` instance.

## Boundary

The theorem does not turn an arbitrary `squareReset` source into the distinguished two-`c` raw
head required by `MM-S67`. The singleton target and deeper generalized history remain live.
Rational denominator clearing preserves mortality, but no theorem yet proves that the restricted
Neary source maps primitive recursively to the cleared integer family. These are independent
mathematical and computability obligations; neither is hidden in the parser.

## Verification

The module and root `MatrixMortality` import build without warnings. Its dedicated namespace lint
passes, LSP reports no diagnostics, and the selected transitive axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`. The forbidden-form scan and diff check pass. The
whole-project linter remains red on pre-existing documentation defects in four unrelated
namespaces and one pre-existing unused typeclass argument. No proof aperture or linter
suppression is present here.

## Artifacts

- [`DecimalSetterBridge.lean`](../MatrixMortality/DecimalSetterBridge.lean)
- [`DecimalSetterMatrix.lean`](../MatrixMortality/DecimalSetterMatrix.lean)
- [`DecimalSetterFracture.lean`](../MatrixMortality/DecimalSetterFracture.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s74-triple-free-bridge-frontier)
