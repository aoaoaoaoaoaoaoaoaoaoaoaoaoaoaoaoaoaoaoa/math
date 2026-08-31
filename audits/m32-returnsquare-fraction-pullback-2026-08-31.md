# M₃(2) ReturnSquare Fraction-Pullback Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S44` synchronizes every positive valuation of a rational composite-base ReturnSquare
root, but says nothing about primes in its denominator. The live question is whether the
negative depths synchronize to one geometric exponent or admit a nonresonant counterexample.

This pass attacks the negative branch without assuming a pure reciprocal. Write the positive
root as `d=A/B`; at a denominator prime, reducedness supplies exactly the unit hypothesis on
`A` used below.

## Exact Pullback

Multiplying the return at `c=−A/B` by `B` gives

```text
G_t = [(B−A)t²−B   Bt]
      [−A           Bt].
```

A dual row `(R,−BS)` pulls through `G_t` by the homogeneous matrix

```text
H_t = [(B−A)t²−B   AB]
      [−t            Bt].
```

Lean proves the matrix intertwining `G_tᵀE_B=E_BH_t` for
`E_B=diag(1,−B)`, then its arbitrary-word form with the required word reversal. Independent
generator scaling contributes the nonzero scalar `−B^(n+1)`. Consequently, for every scale
word `s`,

```text
bridge(A/B,s)=0
  ↔ (H_reverse(s)(A,1))₀ = B(H_reverse(s)(A,1))₁.             (1)
```

Equation (1) is homogeneous. It neither chooses an affine chart nor discards the common content
which may carry the remaining obstruction.

## Terminal Shell

The first pullback sends `(A,1)` to the ray `(At,1)`. In the opposite direction, the target ray
`(B,1)` has homogeneous predecessor

```text
[B(Bt−A), Bt+(B−A)t²−B].                                    (2)
```

Lean checks that applying `H_t` to (2) gives
`B t(B−A)(t²−1)(B,1)`, and proves the cross-multiplied converse. When the second coordinate in
(2) is nonzero, the affine predecessor is therefore unique.

Fix a prime `p` with `vₚ(B)=a>0`, put `vₚ(t)=b>0`, and assume `A` is a unit. The numerator in
(2) has valuation `a`. Its denominator is

```text
(B−A)t² + B(t−1).
```

The summands have valuations `2b` and `a`. If `a≠2b`, the smaller term cannot cancel, so the
unique affine predecessor has

```text
vₚ(P_t)=a−min(2b,a).                                         (3)
```

Thus `a<2b` drains the prime completely; `a>2b` subtracts exactly `2b`; `a=2b` is the only
first-step residue-sensitive shell. At equality, the valuation is nevertheless nonpositive
whenever the affine predecessor is defined. At the geometric scale `t=q^(w+1)`, the tax in (3)
is exactly `2(w+1)vₚ(q)`.

## M₃(2) and M₂(3)

The state in (1) is two-dimensional, but this is not an interreduction to the open
three-generator `2×2` problem. The family `H_(qⁿ)` is an infinite return alphabet cut from the
three modes `1,qⁿ,q²ⁿ`; replacing its members by the three coefficient matrices would replace
matrix products by linear combinations and is unsound. The lawful shared object is the
two-dimensional projective incidence, not a finite semigroup presentation.

## Verdict

| Claim | Disposition | Reason |
|---|---|---|
| every rational fraction has the reversed pullback equivalence (1) | promoted | kernel checked for arbitrary words |
| the terminal predecessor is unique off its displayed pole | promoted | cross-multiplied converse and exact homogeneous image checked |
| noncritical denominator depth obeys (3) | promoted | exact p-adic shells checked |
| the pullback is an `M₂(3)` reduction | rejected | the alphabet still contains every `qⁿ` |
| denominator depths are synchronized | open | repeated critical shells and common reductions can couple primes |
| arbitrary-composite ReturnSquare is classified | open | no recurrence-wide exclusion or exact geometric counterexample |

MASTER VERDICT: arbitrary-composite ReturnSquare remains open

NEW WOUND: every noncritical final inverse step has an exact clipped denominator valuation

EXACT THROAT: control later re-entry from unit or negative predecessor shells, including the common content shared across denominator primes

## Evidence

The formal owner is
[`ReturnSquareFractionPullback.lean`](../MatrixMortality/ReturnSquareFractionPullback.lean).
The focused module build, default namespace linters, transitive axiom inspection, forbidden-
aperture scan, and whitespace gate passed at the recorded commit.
