# M₃(4) Projective-Toggle Line-Atlas Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `5fc433c` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseLineAtlas.lean`](../MatrixMortality/TransverseLineAtlas.lean)

## Verdict

Singular data controls cannot support a genuinely two-dimensional projective history orbit when
the phase toggle is projectively involutive. For arbitrary `B,C,T∈M₃(ℚ)` and `γ∈ℚ³` satisfying

```text
det B = det C = 0,             T² = sI,             s≠0,
```

every raw control word sends `γ` into one of six fixed linear carriers. An arbitrary terminal row
cuts each carrier in the whole carrier or a subspace of vector dimension at most one. This is
uniform over source-dependent controls, row, and column, and it uses the complete free control
monoid rather than intended histories.

The result kills a genuinely two-dimensional projective escape inside this architecture. It does
not decide the nonexpanding projective-line dynamics left inside the six carriers.

## Six-Carrier Normal Form

Let a raw word act from the left. If it contains no data control, repeated toggles reduce through
`T²=sI` to a scalar multiple of `γ` or `Tγ`. If its leading data control is `B` or `C`, that
control absorbs the entire remaining state into its image; an optional leading toggle then moves
the image by `T`. Hence every reachable state belongs to

```text
span(γ),  span(Tγ),  im(B),  T(im(B)),  im(C),  T(im(C)).
```

Lean proves the stronger exact inductive normal form before passing to these carriers. It retains
the boundary scalar and the complete input vector absorbed by a data map, so no projective
division or nonzero-state premise enters the orbit proof.

Lean also defines a canonical carrier label. It records only the parity of the toggles preceding
the first data control and that first data letter; the suffix after it is irrelevant to the
label. Thus the whole-carrier component of any terminal language is finite-mode and regular.

The hypothesis `s≠0` is not needed for the raw linear cover itself. It is retained in the master
theorem because it is exactly what makes `T²=sI` a projective involution rather than a square-zero
collapse. The separate matrix-level involution corollary assumes `T²=I`.

## Dimensions And Terminal Sections

The two boundary carriers have vector dimension at most one. They are rays only when `γ` or `Tγ`
is nonzero. Singularity of `B` and `C` gives

```text
dim im(B) ≤ 2,             dim im(C) ≤ 2.
```

Linear images under `T` cannot increase dimension, so all four data carriers have vector
dimension at most two. They are projective-line charts only when the corresponding carrier has
exact vector dimension two; lower-rank degeneracies remain within the theorem.

For a row functional `λ` and carrier `V`, the terminal section is `V∩ker λ`. If `V≤ker λ`, this
is the whole carrier. Otherwise it is a proper subspace of a space of dimension at most two and
therefore has dimension at most one. Lean proves this dichotomy for every chart.

If `(B,C,T,λ,γ)` is same-zero with `pairedCoefficient ℚ β body`, the row equation and the
six-carrier cover yield the exact equivalence

```text
pairedCoefficient ℚ β body w = 0
  ↔ the state reached by w belongs to the section of its canonical carrier
```

for every raw word `w`. No admissibility, minimum-body, or prescribed-history premise occurs.

## Boundary Of The Cut

This theorem is a geometric reduction, not a decidability theorem for all six-chart systems.
`G3-O04` consumes the result only under its additional hypotheses: one shared integral affine
coordinate, finitely many modes, stationary-or-expanding transitions, bounded translations, and
bounded target coordinates. Under those hypotheses the reverse orbit is finite. Arbitrary
transitions between the rational projective lines are not covered. After removing the regular
whole-carrier component, the exact internal survivor is point reachability in a finite rational
`P¹` atlas. This may coincide with, or feed directly into, the open `M₂(3)` core.

Three exits remain:

1. solve point reachability inside the finite rational `P¹` atlas;
2. use a toggle whose square is not scalar, retaining hidden projective toggle powers;
3. use at least one full-rank data control, which escapes the image-dimension bound.

The same trichotomy constrains the singular same-zero/history compressor needed by the
nine-state binary factor route. An involutive trailing toggle cannot store additional projective
history beyond the six carriers.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every raw orbit lies in six fixed linear carriers when `T²=sI` | promotion | Lean theorem `reachable_mem_carrier` |
| Every word has a canonical carrier determined by finite prefix data | promotion | Lean theorem `wordProduct_mulVec_mem_wordChart` |
| Singular data make every carrier have vector dimension at most two | promotion | Lean theorems `range_finrank_le_two_of_det_zero`, `carrier_finrank_le_two` |
| The boundary carriers have vector dimension at most one | promotion | Lean theorem `boundary_carrier_finrank_le_one` |
| Every row section is whole-carrier or has vector dimension at most one | promotion | Lean theorem `zeroSection_eq_carrier_or_finrank_le_one` |
| The six sections exactly describe any same-zero paired language | promotion | Lean theorem `pairedZero_singular_sixLineAtlas` |
| All six carriers are projective lines | rejected | the boundary carriers are at most rays; data carriers may have rank below two |
| Projective involution means only zero-language invariance under `TT` | rejected | the formal hypothesis is the matrix identity `T²=sI`, `s≠0` |
| The unrestricted six-chart architecture is decidable | rejected | `G3-O04` requires its expanding shared-coordinate normalization |
| `M₃(4)` follows | rejected | nonexpanding line arithmetic and the two structural escapes remain |

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: genuinely two-dimensional projective dynamics with two singular data maps and a
         projectively involutive toggle.
REDUCED: that entire architecture to six fixed rank-at-most-two carriers and six whole-carrier
         or rank-at-most-one terminal sections with a finite-state canonical label.
SURVIVOR: point reachability in the finite rational P¹ atlas, potentially the M₂(3) core;
          non-scalar toggle powers or a full-rank data control escape the atlas itself.
```
