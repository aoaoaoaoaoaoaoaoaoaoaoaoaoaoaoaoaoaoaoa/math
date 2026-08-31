# M₃(4) Mixed-Prime Literal Fork Extinction Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `a4a8fe9` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeLiteralNoGo.lean`](../MatrixMortality/GuardedMixedPrimeLiteralNoGo.lean)

## Verdict

The literal branch of `G3-S08` is impossible. Every exact block-coded mixed-prime realization of
the fixed `bcbc` endpoint language must map the flat and nested fork controls to distinct raw
words inducing the same affine map. Hence it must exhibit a genuine collision in the mixed-prime
affine monoid before the endpoint converse or normalized mantissa is considered.

This does not close the mixed-prime route. A non-common-fixed macro triple may still realize the
forced collision and satisfy the complete arbitrary-word endpoint equation.

## Word Split

Write the data-`b`, data-`c`, and toggle macro words as `x`, `y`, and `z`. Expanding literal
equality of the flat and nested forks and cancelling their common prefix and suffix gives

```text
y z x y x = x z y x y.
```

The two sides split after their first three factors into blocks of equal length. Free-monoid
cancellation therefore gives both

```text
y z x = x z y,       y x = x y.
```

This step holds for lists over an arbitrary alphabet and permits empty macro words.

## Affine Extinction

Exact `bcbc` semantics already makes the actions induced by `x` and `y` distinct. They cannot
both be empty. Choose a nonempty one and let `p` be its rational fixed point. Every nonempty raw
mixed-prime word has slope strictly between zero and one, hence a unique fixed point. The equation
`yx=xy` makes the other macro action fix `p` as well.

Evaluating `yzx=xzy` at `p` yields

```text
Y(Z(p)) = X(Z(p)),       X(p)=Y(p)=p.
```

If `Z(p)≠p`, the affine maps `X` and `Y` agree at two distinct rational points. Their slopes and
intercepts are then equal, contradicting their action-level distinction. Thus `Z(p)=p`; all three
macro actions share `p`. The common-fixed-point obstruction of `G3-S08` then contradicts exact
endpoint semantics.

Consequently the expanded fork words are unequal. `G3-S08` proves their actions equal on all
rational states, so they form a nontrivial kernel pair.

## Search Tax

Both expanded fork words have exact raw length

```text
4(2|x|+|y|+|z|).
```

Lean checks this formula. The published claim that the shortest mixed-prime collision has length
27 is not reproved here. Conditional on that audited classification, every surviving fork
collision has length at least 28 and satisfies `2|x|+|y|+|z|≥7`. The formal result needs no
minimal-collision claim.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The five-factor fork equation splits into the two displayed equations | promotion | Lean list cancellation |
| A nonempty raw word has an explicit rational fixed point | promotion | Lean affine formula |
| Two word actions agreeing at two distinct points agree everywhere | promotion | Lean slope cancellation |
| Distinct `x,y` actions solving the fork equation force a common `x,y,z` fixed point | promotion | Lean composition argument |
| Literal flat/nested word equality is compatible with exact `bcbc` semantics | rejected | common-fixed contradiction |
| Every exact mixed-prime code supplies a genuine kernel collision | promotion | Lean composition with `G3-S08` |
| Every genuine kernel collision fails the endpoint converse | open | no such theorem is claimed |
| `M₃(4)` follows | rejected | the non-common-fixed kernel branch remains open |

## Formal Validation

The owner module and root import compile warning-free under the repository toolchain. The focused
default namespace linter and Lean LSP report no diagnostics. Publication-facing declarations are
listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`. No proof aperture, project axiom, unsafe
declaration, linter suppression, or external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
LITERAL BRANCH: impossible.
MANDATORY WITNESS: distinct flat/nested raw words inducing one affine map.
LENGTH SHAPE: 4(2|κ(b)|+|κ(c)|+|κ(toggle)|).
LIVE ESCAPE: a non-common-fixed genuine kernel triple satisfying the full endpoint converse.
```
