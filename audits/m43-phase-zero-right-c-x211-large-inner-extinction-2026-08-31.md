# M₄(3) phase-zero right-`c` `x=211` large-inner extinction audit

**Date:** 31 August 2026

**Status:** the complete outer-wait-`211` `cb` cylinder is formally extinct

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** eliminate the unbounded inner-wait exit left by M4-S38

## Verdict

For every physical body beginning `cb`, with even total `b` parity, the primitive
phase-zero right-`c` core at outer wait `211` is nonzero for all natural middle and inner
waits. Equivalently, the corresponding residual `b | b | c` bridge determinant is nonzero.

This closes one cylinder. It does not close the phase-zero right-`c` cell or `M₄(3)`:
outer waits below `211` remain outside the theorem.

## Analytic Reduction

Write the tail after the initial `cb` as `c^j b rest`. For the suffix scale `R`, complement
`G`, and explicit affine coefficients `H,J,B`, a core zero gives

```text
GJ = RH − B,
H = 243·3^j(A−39J) − 39J.
```

Since `R>0`, `G≥0`, `J>0`, and `B>0`, the suffix equation forces `H>0`. The sharp global
bound `242G≤39(R−1)` supplies the second affine envelope inequality. For `z≥3^13`, this
envelope, the global theorem `y≤51767`, and exact bilinear rectangle identities prove
`j<13`, `y≥22529`, and the four strips

```text
j=0, 39701≤y≤39830;   j=1, 26337≤y≤26355;
j=2, 23671≤y≤23675;   j=3, y=22898.
```

The remaining positions `4≤j≤12` have incompatible lower and upper middle-wait bounds.

## Exact Certificate

The four strips contain 155 integer pairs. The suffix transitions are

```text
c: H ↦ 3H,
b: H ↦ 243H − 39J.
```

The generator constructs a 231-node decision tree of maximum depth three. Every leaf is one
of four kernel-checked contradictions:

- `H≤0`, incompatible with the positive correction `B`;
- `242H−39J>242B`, beyond the global complement wall;
- both strict inequalities of one first-`b` position gap;
- an empty suffix with `H≠B`.

`scripts/generate-parabolic-first-b-one-inner.py` verifies all affine signs on the complete
ray `z≥3^13`, emits seven bounded Lean shards, and checks their exact source text. The script
is not trusted: Lean normalizes every emitted coefficient and rechecks every tree edge and
leaf. No temporary artifact or heuristic pruning enters the theorem.

## Physical Composition

`bZeroBDefectCOneCodeCore_x211_ne_zero_of_large_inner` combines the suffix certificate with
the exact physical balance. `bZeroBDefectCOneCodeCore_x211_ne_zero` splits on `z<3^13` and
uses M4-S38 on the bounded side. Even total `b` parity forces another `b` in the suffix, so
the final body theorem derives both first- and last-`b` decompositions rather than assuming
them. `bridge_bZero_bTwo_cOne_det_ne_zero_of_cb_x211_even_b_count` transports the result to
the residual determinant.

## Scope And Next Gate

The result has no body-length, suffix-depth, trailing-run, middle-wait, or inner-wait
hypothesis. Its fixed outer wait `x=211` is essential. The next accepted result must prove an
upstream physical reduction `x≤211` for every `cb` zero and then eliminate the full remaining
range `x≤210`. Substituting the endpoint equation `x=211` for that reduction would be a scope
error.

## Validation

The generated-source check, warning-free umbrella build, default namespace linters, Lean LSP
diagnostics, and reviewed axiom-snapshot comparison pass under Lean `4.33.1`. Every
publication-facing theorem draws only from `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, project axiom, unsafe declaration, proof aperture, external declaration, or linter
suppression was added.

## Artifacts

[`MatrixMortality/ParabolicFirstBOneInnerCore.lean`](../MatrixMortality/ParabolicFirstBOneInnerCore.lean),
[`MatrixMortality/ParabolicFirstBOneInnerCertificate.lean`](../MatrixMortality/ParabolicFirstBOneInnerCertificate.lean),
[`MatrixMortality/ParabolicFirstBOneInner.lean`](../MatrixMortality/ParabolicFirstBOneInner.lean),
and
[`scripts/generate-parabolic-first-b-one-inner.py`](../scripts/generate-parabolic-first-b-one-inner.py)
