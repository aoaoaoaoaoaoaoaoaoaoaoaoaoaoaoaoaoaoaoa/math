# M₃(2) Periodic-Shadow Obstruction

Date: 2026-08-06

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. This
ratchet concerns the split-spectrum rank-`(3,2)` guard. The former live attack sought a
coefficient-effective bounded block on which every legal primitive corridor descends in either
the carried prequotient height or the primitive Smith height.

The submitted construction disproves that quantifier. Formal reconstruction found a smaller
family: the large-wait entrance, terminal trap, quotient-factor allocation, and all-place matrix
calculation are unnecessary. One fixed guard already has arbitrarily long legal off-reset
wait-one corridors with arbitrarily long runs of increasing carried and actual primitive Smith
edge coordinates.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the guard `(p,s,A,D,L)=(3,2,17,−5,16)` has ready reset `3/4` fixed by wait one | promotion | formalized |
| the reported itinerary `2K,1^K` gives arbitrarily long primitive corridors | contracted | the entrance is unnecessary; a shorter tail-only family proves the required unbounded corridor theorem |
| every retained tail edge is legal with exact forward content `−4` and Smith coordinate `v=2` | promotion | formalized |
| the carried pair is primitive and its height rises along the tail coordinate run | promotion | formalized |
| the displayed Smith pair is the actual Smith decoder output after exact division by four, is primitive, and rises along the same run | promotion | formalized |
| the entrance puts every moving divisor on the exact-reset quotient side | open, culled | not needed for the obstruction and not promoted |
| the repeated live bridge has all-place factor `10^j` | audited, culled | direct diagonalization is correct, but no Lean API is needed once the witness family kills the target quantifier |
| the reported final state is a trap | open, culled | the checked theorem needs only a finite legal corridor and makes no trap claim |
| coefficient-uniform bounded descent over all legal primitive corridors survives | rejected | the checked family violates it for both retained coordinates |
| reset-started or reverse-terminal descent is also false | open | the construction is deliberately off reset and does not meet a terminal boundary |

## Checked Family

Let `K≥3` be odd. For `1≤n≤K+1` put

```text
t(K,n) = 4 − 9^(K+1) + 10^n 9^(K+1−n),
```

and for `1≤n≤K` put

```text
E(K,n) = (32t(K,n) − 36t(K,n+1), t(K,n)).
```

For every `1≤n<K`, Lean proves that `E(K,n)` and `E(K,n+1)` are primitive and satisfy the exact
wait-one endpoint reduction

```text
E(K,n) --h=−4--> E(K,n+1).
```

Writing `z(K,n)=1+E(K,n).1/(16E(K,n).2)`, the same edge is the actual guard transition

```text
z(K,n) --> z(K,n+1)
```

and its source is ready at wait one. Every state used by the corridor differs from the reset.
The proof does not infer guard dynamics from an integral recurrence: the new generic theorem
`PrimitiveEndpointReduction.guardedStep_endpointState` projectivizes each exact primitive
endpoint reduction to `guardedStep` under the coefficient identities.

The carried primitive pair is

```text
X(K,n) = (t(K,n), −4t(K,n+1)).
```

The Smith split is fixed:

```text
(u,η,θ,v)=(1,−4,20,2).
```

The raw Smith decoder output is exactly four times

```text
Y(K,n) = (8t(K,n)−9t(K,n+1), 4(t(K,n)−t(K,n+1))).
```

Lean proves `X(K,n)` and `Y(K,n)` primitive and

```text
H(X(K,n)) < H(X(K,n+1)),
H(Y(K,n)) < H(Y(K,n+1)).
```

Given any bound `B`, take `length=2(B+1)` and `K=length+1`. Then `K` is odd, `length>B`, and the
states `z(K,1),…,z(K,length+1)` form a legal corridor of exactly that length with all the stated
properties. This is `ReturnGuard.Examples.periodicShadow_obstruction`.

## Shadow Mechanism

The following algebra was independently checked but not installed as a second API. For the
carried ratio

```text
x_n = −4t(K,n+1)/t(K,n),
```

the wait-one transfer is

```text
f(x)=(-76x−160)/(9x),
f(x)+4=−40(x+4)/(9x).
```

The ready-shell fixed ray is `x=−4`. Since `t(K,n)` is a `3`-adic unit and

```text
t(K,n+1)−t(K,n)=10^n9^(K−n),
```

the family has exact shadow depth

```text
v₃(x_n+4)=2(K−n).
```

Each wait-one step spends two units of this unbounded depth. The finite Smith label and constant
wait therefore do not record how long the point will imitate the fixed ray.

The primitive Smith pairs satisfy

```text
Y(K,n+1) = [[1,1/2],[0,10/9]] Y(K,n).
```

The matrix diagonalizes over `ℚ` with eigenvalue ratio `10/9`. Its projective all-place sup
factor is

```text
max(1,10/9) · max(1,|10/9|₃) = (10/9)·9 = 10,
```

and the factor for a `j`-step block is `10^j`, not at most one. This rules out repairing the
all-legal descent claim merely by multiplying the real and finite-place norms of this live
Smith coordinate.

## Scope

The reset is ready and fixed, while every state of the constructed corridor is off reset. The
theorem therefore refutes descent over all legal corridors, not descent along the unique orbit
started at reset. That orbit is the displayed nonterminal fixed point. The construction neither
builds an infinite unbounded-denominator orbit nor reaches terminal, and it does not decide the
full rank-`(3,2)` artery, the exceptional rank-`(2,2)` compiler seam, or `M₃(2)`.

The coordinate inequalities also refute every coefficient-uniform assertion that some bounded
nonempty prefix of every legal corridor decreases either displayed edge height: choose the
checked corridor sufficiently longer than the asserted bound, so every coordinate required by
that prefix belongs to two consecutive legal edges and ends higher than it begins.

## Culling

The reported large-wait entrance, finite-state-selector formulation, live two-Smith bridge,
all-place factor, fresh-prime allocation, and eventual trap were not installed. None is needed
once the shorter tail family directly kills the all-corridor theorem. All proof-only arithmetic
lemmas in the new Lean module are private; the public surface consists of the family data, the
fixed Smith split, and the obstruction theorem.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GUARD VERDICT: the reset-started even-reset-defect unbounded-denominator stratum remains open
REMOVED: coefficient-uniform bounded descent over all legal primitive corridors, in both carried and primitive Smith height
REMAINS: reset- or terminal-history-sensitive control of unbounded periodic-shadow depth on the actual physical orbit
DISTANCE: prove an effective reset-anchored first-hit-terminal bound, or construct one fixed reset orbit that concatenates shadow episodes into an infinite unbounded-denominator execution
```

## Artifact

The generic projectivization theorem is in
[`ReturnGuardCumulative.lean`](../MatrixMortality/ReturnGuardCumulative.lean). The fixed family
and obstruction theorem are in
[`ReturnGuardPeriodicShadow.lean`](../MatrixMortality/ReturnGuardPeriodicShadow.lean).
