# M₄(3) phase-zero right-`c` later-first-`b` extinction audit

**Date:** 1 September 2026

**Status:** first-`b` positions three through eleven are empty

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** eliminate every even/even mixed body whose first `b` follows 3 through 11 leading
copies of `c`

## Verdict

Let the physical body be `c^k b tail`, where `3≤k≤11` and `tail` contains `b`. Its primitive
phase-zero right-`c` core is nonzero at every natural outer, middle, and inner wait. Even total
`b` parity forces the tail-membership hypothesis, so none of these nine body cylinders closes
the residual `b | b | c` bridge.

Together with the previously checked unary, long-prefix, `cb`, and `ccb` theorems, only the
leading-`b` cylinder remains in the even-length/even-`b` phase-zero right-`c` rectangle. This
audit does not claim that cylinder, the complete phase-zero cell, or M₄(3) is closed.

## Main Stratum

Tail-scale normalization turns a core zero into exact rational outer- and inner-root equations.
For middle wait `y≥2`, exact lower and upper outer-root graphs plus the global middle-wait bound
leave 44 integral `(k,x,y)` points:

```text
k=3: (209,17), (210,21), (211,27), (212,38),
     (213,64..66), (214,206..236)
k=4: (213,18), (214,43..45)
k=5: (214,13)
k=6: (213,2)
k=7..11: none
```

Decomposing `tail=c^j b rest` gives exact rectangles for small `j` and one stabilized envelope
for every later `j`. The deterministic certificate contains 66 rectangle leaves. Each leaf
proves either that the inner root is negative or that it lies strictly between consecutive
integers. Lean rechecks every rational corner and contradiction.

## Boundary Strata

At `y=0`, positions `k=3,4` lie in the strict positive complement cone. Exact outer-root
rectangles for `5≤k≤11` leave only `(k,x)=(5,351)` and `(8,218)`. The latter inner root lies in
`(0,1)`. The former forces `j=1,z=2`, hence the exact endpoint word `cccccbcb`; its primitive
core contradicts the strict suffix-density gap.

At `y=1`, the outer-root rectangles leave only `(k,x)=(4,184)`. Its inner equation forces
`j=0,z=4`, hence `ccccbb`, whose core contradicts the position-zero suffix-density gap.

These arguments are theorem-level reductions. They do not rely on a search depth, sampled
words, or a hidden wait cap.

## Trust Boundary

The generator uses exact `Fraction` arithmetic to choose complete tail-position partitions and
emits ordinary Lean. Generated leaves invoke only proved rectangle and integral-gap theorems;
`norm_num` rechecks all closed rational inequalities. The generator is a theorem producer, not
an oracle, and contributes no axiom.

The 44-point outer classifier, the zero- and one-wait analytic reductions, the two exact
endpoint contradictions, and the physical composition are handwritten Lean. No claim in the
final theorem depends on the provisional leading-`b` census.

## Validation

The analytic modules, four generated shards, aggregate certificate, boundary reductions, and
physical closure build without warnings under Lean `4.33.1`. Deterministic regeneration, Ruff,
formatting, `ty`, the project lint audit, and the reviewed transitive axiom snapshot pass.
No proof aperture, external declaration, unsafe definition, or linter suppression is present.

## Artifacts

[`MatrixMortality/ParabolicFirstBLateCore.lean`](../MatrixMortality/ParabolicFirstBLateCore.lean),
[`MatrixMortality/ParabolicFirstBLateReduction.lean`](../MatrixMortality/ParabolicFirstBLateReduction.lean),
[`MatrixMortality/ParabolicFirstBLateTailCore.lean`](../MatrixMortality/ParabolicFirstBLateTailCore.lean),
[`MatrixMortality/ParabolicFirstBLateCertificate.lean`](../MatrixMortality/ParabolicFirstBLateCertificate.lean),
[`MatrixMortality/ParabolicFirstBLateBoundary.lean`](../MatrixMortality/ParabolicFirstBLateBoundary.lean),
[`MatrixMortality/ParabolicFirstBLateClosure.lean`](../MatrixMortality/ParabolicFirstBLateClosure.lean),
and
[`scripts/generate-parabolic-first-b-late-tail.py`](../scripts/generate-parabolic-first-b-late-tail.py)
