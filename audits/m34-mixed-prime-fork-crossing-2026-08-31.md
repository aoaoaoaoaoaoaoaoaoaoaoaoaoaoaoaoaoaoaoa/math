# M₃(4) Mixed-Prime Fork-Crossing Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `df2f6b6` on `wave3-m34-transverse`
**Formal owner:**
[`GuardedMixedPrimeForkCrossing.lean`](../MatrixMortality/GuardedMixedPrimeForkCrossing.lean)

## Verdict

The reduced five-factor fork equation is exactly one crossing transport. If the data actions are

```text
X(t)=at+(1-a)p,       Y(t)=bt+(1-b)q,
```

with `a≠b`, let `τ` be the crossing of `X,Y` and `σ` the crossing of `XYX,YXY`. For every affine
toggle `Z`, Lean proves

```text
Y Z X Y X(t) - X Z Y X Y(t) = (b-a)(Z(σ)-τ).
```

Thus equality on every state is equivalent to `Z(σ)=τ`. For physical contractions, Lean also
classifies the strict order of the two data fixed points, `σ`, `τ`, and the toggle fixed point.

This order does not produce a raw-word address descent. At every depth `n`, two distinct words
with leading translation runs `n` and `n+2` induce exactly the same mixed-prime affine action.
They are the two sides of Cassaigne's relation after a common `Tⁿ` prefix. Lean also proves the
exact slope-conditioned fixed-point cylinder for every `TⁿD`-headed word. Therefore affine
action data cannot choose a leading-run representative; an unbounded obstruction must work in an
oriented quotient of the kernel.

## Crossing Factorization

The two crossings are

```text
τ = ((1-a)p-(1-b)q)/(b-a),
σ = ((1-a)p(ab²-ab+b)+(1-b)q(-a²b+ab-a))/(b-a).
```

Direct rational normalization gives

```text
σ-τ = (1-a)(1-b)(1+ab)(p-q)/(a-b),
τ-q = (a-1)(p-q)/(a-b),
τ-p = (b-1)(p-q)/(a-b).
```

The formal theorem proves the five-factor difference identity for every rational state. Since
`b-a≠0`, it proves both directions of the equivalence between equality of the affine actions and
`Z(σ)=τ`. The word-action specialization uses the canonical slope and fixed point of each macro;
the `bcbc` endpoint theorem supplies the required unequal data slopes automatically.

## Complete Order

Assume `0<a,b,c<1`, `a≠b`, `p≠q`, and `Z(σ)=τ`. Lean proves exactly one of four chains:

```text
b<a, p<q:       p<q<σ<τ<r;
b<a, q<p:       r<τ<σ<q<p;
a<b, q<p:       q<p<σ<τ<r;
a<b, p<q:       r<τ<σ<p<q.
```

In each orientation, the fixed point of the smaller-slope data action lies between the other
data fixed point and the toggle fixed point. The new information is that `σ` and `τ` occupy the
two consecutive interior positions between that data fixed point and the toggle fixed point.

## Address Ambiguity

Let `ℓ(w)` be the number of initial `T` letters before the first `D`. For each `n`, define

```text
Lₙ=Tⁿ cassaigneLeft,       Rₙ=Tⁿ cassaigneRight.
```

Lean proves

```text
Lₙ≠Rₙ,       wordAction(Lₙ)=wordAction(Rₙ),
ℓ(Lₙ)=n,     ℓ(Rₙ)=n+2.
```

The ambiguity is therefore unbounded in address and persists after every common translation
prefix. It is not a numerical collision found by search.

For a word `w=TⁿD v`, put

```text
eₙ=(5/2)(1-(3/5)ⁿ),       sₙ=(2/3)(3/5)ⁿ,       g=wordScale(w).
```

Lean proves the exact cylinder

```text
eₙ/(1-g) ≤ wordFixedPoint(w)
            ≤ [eₙ+(5/2)(sₙ-g)]/(1-g).
```

Both sides of the prefixed Cassaigne relation have the same `g` and fixed point but occupy the
`n` and `n+2` cylinders. Fixed-point order, slope, and the 2-adic parity of the leading run are
therefore compatible with multiple raw addresses. A descent using any of these action invariants
alone is ill-defined.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The five-factor affine difference has the displayed factorization | promotion | Lean rational identity |
| Unequal data slopes make the fork equality equivalent to `Z(σ)=τ` | promotion | Lean cancellation of `b-a` |
| The four displayed physical order chains are exhaustive | promotion | Lean linear order and positivity |
| Every `TⁿD`-headed word satisfies the displayed fixed-point cylinder | promotion | Lean interval invariance and fixed-point algebra |
| Equal mixed-prime actions determine the leading translation run | rejected | formal prefixed Cassaigne counterfamily |
| Fixed slope and fixed point determine the leading translation run | rejected | the same formal counterfamily |
| Leading-run parity plus the crossing order yields a raw-word descent | rejected as stated | parity survives the `n↔n+2` ambiguity |
| No reduced fork triple exists | open | no quotient-normal-form obstruction is yet proved |
| A reduced fork triple satisfies the endpoint converse | open | crossing transport is necessary, not sufficient |
| `M₃(4)` follows | rejected | the kernel quotient and normalized mantissa remain open |

## Formal Validation

The formal owner and root module compile warning-free under the repository toolchain. The focused
default namespace linter and Lean LSP report no diagnostics. Publication-facing declarations are
listed in [`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom sets agree with the
reviewed project baseline. No proof aperture, project axiom, unsafe declaration, or linter
suppression is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
EXACT FORK EQUATION: Z(crossing(XYX,YXY))=crossing(X,Y).
ORDER: the two crossings fill the interval before the exterior toggle fixed point.
NO-GO: affine action data cannot decode a raw leading run, even modulo parity.
LIVE ESCAPE: orient the mixed-prime kernel and exclude or construct a quotient fork survivor.
```
