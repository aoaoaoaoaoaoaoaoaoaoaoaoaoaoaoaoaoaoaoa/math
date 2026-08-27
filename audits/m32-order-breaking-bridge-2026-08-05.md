# M₃(2) Order-Breaking Bridge Audit

Date: 2026-08-05

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. In
the split-spectrum rank-`(3,2)` guard, every genuinely nonperiodic residue has even reset
resultant, passes the universal-boundary walls, and has unbounded reduced denominators. The live
enemy is global amortization of the mandatory nonmaximal Smith branches against inherited
rational height.

The attack under review proposed a narrower cyclotomic program: enter an auxiliary-prime reset
ball at a wait divisible by the base's exact order, then charge the first wait outside that
order.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| exact primitive multiplicity is a difference of reset-defect and pole valuations | restatement | follows from the checked endpoint factorization and complete cancellation law; no duplicate declaration is retained |
| arbitrarily deep surviving reset congruences can stop on the ball boundary | correct, culled | sharpens a local implication but has no remaining consumer after the bridge failure below |
| a legal order-breaking bridge can eject the reset ball without auxiliary-prime cancellation | promotion | a smaller coefficient law is now kernel checked |
| the submitted bridge defeats a theorem conditioned on continued survival | rejected | its target is a base-prime unit in the permanent trap |
| a ready bridge target can still eject the ball and amplify denominator height | promotion | found during formalization and checked by `orderBreaker_shatters_resetBall` |
| the first bridge supplies a uniform irreversible local debit | rejected | the checked ready target loses no auxiliary-prime content and its denominator grows from `19` to `270178` |
| exact-order bridges alone are a strictly narrower route than global amortization | rejected | any surviving replacement must amortize an unbounded bridge sequence and is therefore global again |

## Normalization Is Already Owned

For an endpoint source `z=x/y`, put `q=pᵃ`, `R=A+D−L`, and

```text
M = x−L(q−1)y,
N = (A−L+Dq²)x−(A−L)L(q−1)y.
```

The checked endpoint factorization gives

```text
Δ = N−RM = D(q−1)((q+1)x+Ly).
```

Since `(N,M)=(N−RM,M)` as integer ideals, a primitive reduction by
`c=gcd(N,M)` satisfies, at every auxiliary prime `ℓ≠p`,

```text
vℓ(c)=min(vℓ(M),vℓ(Δ)),
vℓ((N/c)−R(M/c))=max(vℓ(Δ)−vℓ(M),0),
vℓ(M/c)=max(vℓ(M)−vℓ(Δ),0).
```

Equivalently,

```text
vℓ(F_q(z)−R)=vℓ(Δ)−vℓ(M).
```

This is the endpoint gauge of the existing exact cancellation theorem
`integralStep_commonFactor_padicValInt`, not a second normalization mechanism. Reifying it as a
parallel API would duplicate the checked content calculus.

## A Live Bridge Ejection

Formalization found a smaller witness than the submitted parametric family. Take depth two and

```text
p=3,   A=R=249398,   D=L=1,
center=249398,        reset state=249399.
```

The reset is ready at wait four:

```text
249399 = 3⁴·3079,
249399−3⁴ = 3⁸·38.
```

The first two guarded steps are

```text
249399 ─4→ 4863261/19 ─1→ 67384284465/270178.
```

Both sources are ready at their displayed waits, and the second target is itself ready at wait
one. Thus the order-breaking bridge occurs on a genuinely continuing legal prefix, not on a
branch entering the permanent trap.

The auxiliary prime `5` is a primitive divisor of `3⁴−1`; hence `3` has exact order four
modulo `5`, and wait one breaks that order. In endpoint coordinates `z=state−1`,

```text
v₅(R)=0,
v₅(z₁−R)=1,
v₅(z₂−R)=0.
```

The first step enters the strict reset ball, and the live bridge ejects it to the boundary. The
raw bridge action is

```text
endpointTransfer(3,2,249398,1,1,1) · (4863242,19)
  = (1212912257166,4863204).
```

Its coordinate gcd is exactly `18`, coprime to `5`, and reduction gives the endpoint pair
`(67384014287,270178)`. No `5`-content is swallowed; the primitive denominator grows from `19`
to `270178`. The branch determinant is `−18`, also a `5`-adic unit.

The coefficient law lies on the intended residue: `R=2·124699` is even. At the sole prime of
`p−1`, the first universal-boundary inequality is saturated rather than strict; at every odd
prime its right-hand boundary valuation is zero. Thus no checked universal-boundary wall removes
the witness.

Artifact: `ReturnGuard.Examples.orderBreaker_shatters_resetBall` in
[`ReturnGuardExamples.lean`](../MatrixMortality/ReturnGuardExamples.lean).

## Culling

The submitted 507-step family, its separate endpoint-map definition, bridge semigroup prose,
and a duplicate valuation-normalization API were not retained. The checked corpus already owns
the general factorization and cancellation theorem. One ready-target witness is the smallest
artifact needed to kill uniform first-bridge closure.

The submitted example's target was a permanent trap, so it could not support the report's
global conclusion. That defect was repaired rather than silently inherited.

## Wound

```text
MASTER VERDICT: still open
REMOVED: every proof which assigns a uniform invariant-ball, auxiliary-content, repetition, or denominator-descent charge to the first order-breaking bridge, even when its target remains ready
REMAINS: global amortization across an unbounded sequence of moving-frame nonmaximal branches, or an exact infinite unbounded-denominator counter-orbit
DISTANCE: prove one fixed global height/content law over complete surviving executions, or construct and isolate a computable infinite execution; exact-order bridges have no independent local closure
```
