# Formal Decimal Setter Compiler Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the explicit decimal setter, its regular forward compiler, integer clearing, and
delimiter-cube fracture are formalized; the arbitrary-word converse is not proved

## Matrices

`DecimalSetterMatrix.lean` evaluates binary words in radix ten with digits `0↦7,1↦5` and
conjugates the side correspondence by the audited boundary basis. The resulting data matrices
are `A_b,A_c`. The delimiter is exactly

```text
[[1,0,0, 0,0],
 [0,1,0,−1,λ],
 [0,0,1, 0,−1],
 [0,1,0,−1,λ],
 [0,0,1, 0,−1]].
```

Lean proves `rank S=3`, `rank S²=2`, `rank S³=1`, and `Sⁿ=S³` for every `n≥3`. It also proves
the internal separator identity `S²A_cS³=λC̃L̃`. In particular, the formal delimiter does not
satisfy `S³=S`; its cube is the stabilized rank-one matrix.

## Regular Compiler

`RegularSpelling` decodes every physical word in which data letters are separated by at most one
delimiter. No delimiter immediately to the right selects the rule role; one delimiter selects
the erasure role; the marked terminal column makes the final data letter an erasure. The
resulting scalar is exactly

```text
code(upper ++ marker) − code(lower).
```

Every Neary terminal match has such a spelling. Sandwiching it between two internal-separator
words gives an explicit zero product, so restricted Neary halting implies rational setter
mortality.

`RationalMatrixClearing.lean` multiplies each finite rational matrix by the product of all entry
denominators and records the corresponding integer matrix. Casting recovers the independently
scaled rational family, and nonzero generatorwise scaling preserves mortality.
`DecimalSetterInteger.lean` applies this construction to an explicit equivalence between three
labels and `{S,A_b,A_c}`. Thus Neary halting implies mortality of a transparent three-generator
integer `5 × 5` family.

## Arbitrary Products

`DecimalSetterFracture.lean` greedily splits any physical word at disjoint occurrences of
`S³`. Exact word-product reconstruction uses no regularity assumption. If at least one triple
occurs, the whole product is

```text
(product of interior bridge scalars) · (exterior column) (exterior row).
```

This reduces a zero containing delimiter cubes to a zero bridge coefficient or a vanishing
exterior factor. It does not classify a triple-free bridge: such a chunk may contain isolated
delimiters and maximal delimiter runs of length two in arbitrary positions.

## Boundary

The mortality converse requires a maximal-run parser connecting each triple-free bridge to the
existing projective transfer and pole equations. The current arithmetic extinction proves that
one distinguished non-singleton raw-head entry into a multi-role pole is impossible. It does not
yet exhaust singleton next targets, generalized carriers, or every ordinary-reset history.

The integer family is definitionally computable, but no Lean theorem yet proves its dependence
on the source primitive recursive. Consequently this audit does not yield a many-one reduction
or undecidability of `M₅(3)`.

## Verification

The four narrow modules build without warnings. The root import, namespace lint, selected
transitive axiom audit, forbidden-form scan, and diff check are the integration gates. No proof
aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterMatrix.lean`](../MatrixMortality/DecimalSetterMatrix.lean)
- [`DecimalSetterFracture.lean`](../MatrixMortality/DecimalSetterFracture.lean)
- [`RationalMatrixClearing.lean`](../MatrixMortality/RationalMatrixClearing.lean)
- [`DecimalSetterInteger.lean`](../MatrixMortality/DecimalSetterInteger.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-m06-formal-decimal-setter-compiler)
