# M₃(2) ReturnSquare Weighted-Tail Adjugate Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

Positive numerator valuations are synchronized by `R32-S44`, but the bridge word still appears
to have an unbounded head exponent. This audit separates the head from the proper tail without
entering an affine chart.

## Adjugate Identity

For the fraction pullback `H_t`, define

```text
J_t = [Bt   −AB]
      [t    (B−A)t²−B].
```

Direct expansion proves `(H_t x)∧y=x∧(J_t y)`. Reversal of the `H` word is exactly canceled by
the forward order of the `J` word, so the identity iterates over arbitrary tails.

## Head Separation

The head pullback sends `(A,1)` to a nonzero scalar multiple of `(Aq^(head+1),1)`. If

```text
(R,S) = J_tail · (B,1),
```

the complete bridge is zero exactly when

```text
R=Aq^(head+1)S.                                            (1)
```

Equation (1) is homogeneous and remains valid when an intermediate affine denominator
vanishes.

## Finite Tail Weight

If `vₚ(A/B)=k vₚ(q)>0`, `R32-S44` fixes the proper-tail wait exponent to `k`. There are only
finitely many lists of positive wait exponents summing to `k`; each yields one rational pair
`(R,S)`, after which (1) is one exact base-power membership test. This removes arbitrary head
enumeration from every positive-valuation branch. The formal theorem states the fixed weight
and incidence; the finite enumeration is its immediate combinatorial consequence.

## Exact Search

An exact implementation enumerated every tail composition of weight at most eighteen, with
denominator-prime exponent at most one hundred, for `q∈{6,10,12,18}` after the `R32-S48`
filters. It tested the head by exact base-power membership and found no nonresonant zero. This is
reconnaissance, not theorem evidence.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| affine poles invalidate reverse-tail enumeration | rejected | the adjugate certificate is homogeneous |
| positive numerator branches require an unbounded word search | rejected | their complete tail weight is fixed |
| the head exponent must be enumerated | rejected | it is one exact cyclic-ray membership test |
| pure-denominator branches are bounded by the same argument | rejected | no positive valuation fixes their tail weight |
| arbitrary-composite ReturnSquare is classified | open | the pure-denominator residue graph remains |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every positive-numerator candidate has a finite exact tail certificate

EXACT THROAT: decide or exclude the pure-denominator common-base branch

## Evidence

The formal owner is
[`ReturnSquareTailAdjugate.lean`](../MatrixMortality/ReturnSquareTailAdjugate.lean). The focused
module build, umbrella build, default namespace linters, transitive axiom inspection, Lean LSP
diagnostics, forbidden-aperture scan, and whitespace gate passed at the recorded commit.
