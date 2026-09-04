# M₄(3) phase-zero right-`c` lower-range classification audit

**Date:** 1 September 2026

**Status:** every physical `cb` zero with `x≤210` lies in one of five exact suffix chambers

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** classify the complete lower outer-wait range left by M4-S40

## Verdict

For a physical body beginning `cb` whose remaining tail contains `b`, a primitive core zero
with `x≤210` forces one of exactly five tuples or rays:

```text
(206,0,162,7), (206,0,162,8), (207,2,202,1),
(210,1,802,4), (210,0,812,9),
(210,1,801,z) with z≥380.
```

Here `j` is the number of leading `c` letters in the tail before its first `b`. This is an
exact classification theorem. It does not assert that any displayed chamber contains a zero.

## Analytic Reduction

Write `T` and `E` for the scale and complement of the tail after the initial `cb`, and set

```text
a = 729(72y−9)+(9−8y)/T,
d = 39+E/T.
```

The core equation is one rational outer-root equation. Tail grammar gives

```text
729(72y−9)+(9−8y)/243 ≤ a ≤ 729(72y−9),
39 ≤ d ≤ 9477/242.
```

Monotonicity in `a`, `d`, and the inner wait encloses the integral outer wait between two
explicit rational graphs. Under `x≤210`, exact cross multiplication leaves 22 compressed
ranges containing 113 `(x,y)` pairs. Middle waits zero and one are excluded separately.

## Exact Certificate

Decompose the tail as `c^j b rest`. Exact and stabilized density rectangles bound `a,d` for
each of the 113 pairs. Affine corner signs either put the inner root in an open interval between
consecutive integers, make it negative, or yield one of the five displayed chambers. The sole
ray is certified by positivity of both its root numerator and `N−379D`; the root equation
`N=Dz` then gives `z≥380`.

The generator performs exact rational arithmetic only and emits ordinary Lean proofs. Lean
rechecks every rectangle corner with `norm_num`; the generator is not in the trusted base.

## Scope

No sampled suffix length, trailing-run bound, or inner-wait cap is used. The theorem assumes
the `cb` prefix, `x≤210`, and that the remaining tail contains `b`. It classifies the lower
range but does not eliminate the five terminal chambers or close the full `cb` cylinder.

## Validation

The generated aggregate and physical composition build without warnings under Lean `4.33.1`.
All shards contain fewer than 1,500 lines. The generator passes deterministic regeneration,
Ruff, formatting, and `ty` checks. Publication-facing declarations are included in
`AxiomAudit.lean`; no proof aperture, external declaration, unsafe definition, or linter
suppression is present.

## Artifacts

[`MatrixMortality/ParabolicFirstBOneOuterCore.lean`](../MatrixMortality/ParabolicFirstBOneOuterCore.lean),
[`MatrixMortality/ParabolicFirstBOneOuterCertificate.lean`](../MatrixMortality/ParabolicFirstBOneOuterCertificate.lean),
[`MatrixMortality/ParabolicFirstBOneOuter.lean`](../MatrixMortality/ParabolicFirstBOneOuter.lean),
and
[`scripts/generate-parabolic-first-b-one-outer.py`](../scripts/generate-parabolic-first-b-one-outer.py)
