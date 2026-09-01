# M₄(3) phase-zero right-`c` outer-wait cap audit

**Date:** 31 August 2026

**Status:** every physical `cb` bridge zero has outer wait at most `211`

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** reduce the unbounded outer-wait axis to the range already separated by M4-S39

## Verdict

For every physical body beginning `cb`, if the primitive phase-zero right-`c` core vanishes,
then its natural outer wait satisfies `x≤211`. The same implication holds when stated as a
zero of the residual `b | b | c` bridge determinant.

M4-S39 eliminates the endpoint `x=211`. Therefore every remaining zero in this cylinder must
satisfy `x≤210`. This audit does not assert that the lower range is empty.

## Exact Argument

Write `S` for the ternary scale and `D=S−C−1` for the complement. A body beginning `cb`
has positive complement and obeys the first-`b` density inequality

```text
13S ≤ 243D.
```

If the middle wait is zero, the same inequality implies `S−1≤585D`, and M4-S30 makes the
core strictly positive. Suppose instead that the middle wait is positive. The core is strictly
increasing in `x`. Its value at `(x,y)=(212,0)` is positive because the root pencil is

```text
−(345710276z+31669705)
```

and both terms of the thin-complement decomposition are positive. Let `T=243D−13S≥0`.
The middle-wait slope at `x=212` satisfies

```text
243·slope = S(2020784785920z+199972684656)
              +T(620717828832z+58005064872)
              +(672060776544z+61565906520).
```

For natural `z`, the first and third terms are positive and the middle term is nonnegative.
Hence the core is positive at `x=212` for every positive middle wait, and outer monotonicity
keeps it positive for every `x≥212`.

## Scope

No body-length, parity, suffix, middle-wait, or inner-wait bound is assumed. The result applies
only to bodies beginning `cb` and only bounds the outer wait; it neither proves nonvanishing in
the residual `x≤210` range nor closes the complete phase-zero right-`c` cell.

## Validation

`MatrixMortality.ParabolicWaitBounds` builds without warnings under Lean `4.33.1`. The three
publication-facing declarations are included in `AxiomAudit.lean`; their transitive axiom sets
are compared with the reviewed snapshot. No proof aperture, external declaration, unsafe
definition, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicWaitBounds.lean`](../MatrixMortality/ParabolicWaitBounds.lean)
