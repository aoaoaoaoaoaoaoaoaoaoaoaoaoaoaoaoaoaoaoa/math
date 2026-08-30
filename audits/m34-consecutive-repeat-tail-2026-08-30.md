# Consecutive-Repeat Tail Audit

**Date:** 2026-08-30

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `9f44e7edcb0e0e42f890a1ce191b1e4b7b32ba14`

## Verdict

A fixed-boundary free-monoid equation cannot accept two consecutive exponents of one stationary
pump and later reject an exponent. This closes the unary consecutive-zero lower-bound shortcut
for the `M₃(4)` positive-transition lane. It does not close the lane itself.

## Theorem

For words `A,B,C,D,E,F` over any alphabet and natural numbers `N,k`, assume

```text
A Bᴺ C = D Eᴺ F,
A Bᴺ⁺¹ C = D Eᴺ⁺¹ F.
```

Then

```text
A Bᴺ⁺ᵏ C = D Eᴺ⁺ᵏ F.
```

Lean proves this as `fixedBoundary_consecutive_repeat_tail` in
[`WordMorphism.lean`](../MatrixMortality/WordMorphism.lean).

## Proof

Absorb the first `N` copies into the two left boundaries, reducing to exponents zero and one.
The exponent-zero equality makes the two left boundaries prefix-comparable.

If `D=AG`, right cancellation gives `C=GF`. Substitution into the exponent-one equality and
cancellation on both ends gives `BG=GE`. Induction yields `BᵏG=GEᵏ`, hence

```text
A Bᵏ C = A Bᵏ G F = A G Eᵏ F = D Eᵏ F.
```

If `A=DG`, the symmetric cancellations give `F=GC` and `GB=EG`. Thus `GBᵏ=EᵏG`, and the same
conclusion follows. These are the only cases by prefix comparability in a free monoid.

## Lower-Bound Consequence

For a fixed unary matrix transition in dimension three, Cayley-Hamilton makes every scalar
coefficient satisfy an order-at-most-three recurrence. A standard lower-bound certificate would
therefore seek three consecutive language zeros followed by a nonzero escape. When the language
is literal equality of two fixed-boundary morphic words along a repeated source block, the
displayed theorem forces every later exponent from the first two equalities. That certificate
cannot occur.

The obstruction is exactly unary and stationary. It leaves multiple noncommuting pump blocks,
interleaved shifts, exponent-dependent terminal sections, and matrix zero languages not induced
by literal word equality untouched.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Two consecutive fixed-boundary pump solutions force the whole tail | promotion | Lean theorem `fixedBoundary_consecutive_repeat_tail` |
| A unary consecutive-zero Cayley-Hamilton certificate can lower-bound these equations | rejected | the promoted tail theorem |
| Every positive projective transition lower bound is impossible | rejected | noncommuting and nonstationary shifts remain |
| `M₃(4)` follows | rejected | no source-uniform three-state compiler or four-state obstruction |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: stationary unary consecutive-repeat escape as a dimension-four certificate.
REMAINS: source-uniform singular recognition, or a genuinely interacting shift obstruction.
```
