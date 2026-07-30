# M₃(2) Endpoint-Content Audit

## Question

What survives after the Cramer and tangent coordinates are recognized as gauges, and which
arithmetic resource can still carry an unbounded computation in the guarded return family?

## Terminal Gauge

For an integral presentation `α=A/L`, `ρ−α=D/L`, the coordinate

```text
x = L(z−1) = A−L+D/w
```

is a fixed linear gauge of the residual pair. Reset is `A+D−L`; terminality is `x=0`. A wait
`a` acts by

```text
Mₐ =
  [ A−L + Dp^(sa)   −(A−L)L(pᵃ−1) ]
  [ 1                −L(pᵃ−1)       ],
```

and

```text
det Mₐ = −DLp^(sa)(pᵃ−1).
```

Lean checks the conjugacy to the existing residual transfer and the complete word determinant
factorization.

## Complementary Contents

Suppose a primitive step removes signed content `h`, and define `k` by

```text
h k = DL(pᵃ−1).
```

The explicit adjugate sends the reduced target ray back to the source ray with scalar `−k`.
For a complete terminal word, determinant comparison gives the global endpoint law

```text
first-row coefficient = (−1)^N ∏ kᵢ.
```

The endpoint and primitive normalization therefore retain both halves of every cyclotomic
determinant. The former tangent projective coordinate contains no independent state and was
deleted with its localization and collision-ladder apparatus.

## Coefficient Boundaries

At `A−L=0`, endpoint transport preserves a nonzero first coordinate whenever drift and base
survive. Consequently, any prime dividing `A−L` but neither `D` nor `p` certifies immortality.
This compact theorem excludes:

- the period-three survivor at prime 31;
- the former four-step collision-ladder candidate at prime five.

The scale and drift specializations are also exact whole-word product identities. They expose
the finite subgroup tests still to be packaged as executable classifiers.

The aligned residue is nonempty. Lean checks two genuine two-step terminal guards with wait
words `[3,1]` and `[2,3]`; neither one-step mortality nor monotone wait descent is a lawful
global invariant.

## Adelic Budget

If `(M,N)=h(m′,n′)` is one primitive reduction, then

```text
|h|H(m′,n′) ≤ C H(m,n),
p^((s−1)a)|h| ≤ C H(m,n),
C=|A|+|D|+|L|.
```

Every part of `pᵃ−1` coprime to `h`, including multiplicity, divides `m′−n′`. For two
trajectories through one branch, Lean checks the exterior-product conservation law

```text
p^(sa) g h (v′∧u′) = DL(1−pᵃ)(v∧u).
```

Exact branch similarity also yields arbitrary repeated-factor pumping: the same legal block at
two checkpoints either begins at the same rational state or its p-adic expansion weight is
bounded by the two projective height envelopes.

## Remaining Boundary

For a reduced endpoint state `xᵢ=rᵢ/tᵢ`, let `qᵢ=p^aᵢ`, let `hᵢ` be its signed forward
content, and put `kᵢ=DL(qᵢ−1)/hᵢ`. Consecutive readiness equations give

```text
qᵢ₊₁^s hᵢ₊₁ tᵢ₊₂
  = (A + Dqᵢ^s − Lqᵢ₊₁)tᵢ₊₁ + kᵢtᵢ.
```

This repairs an earlier sketch which had dropped `hᵢ`. Suppose `1≤tᵢ≤B` along an infinite
orbit and write a nondecreasing transition as `aᵢ₊₁=aᵢ+η`. Dividing the recurrence by `qᵢ`
gives

```text
(Atᵢ₊₁+kᵢtᵢ)/qᵢ
  = Lp^ηtᵢ₊₁
    + qᵢ^(s−1)(p^(sη)uᵢ₊₁−Dtᵢ₊₁),
```

where `uᵢ₊₁=hᵢ₊₁tᵢ₊₂` is a p-adic unit. The left side is an integer of bounded absolute value:
`|kᵢ|≤|DL|(qᵢ−1)` and both denominators are bounded.

If `η<(s−1)aᵢ`, the two right summands have distinct p-adic valuations. Hence `η` is bounded.
For large `qᵢ`, boundedness then forces
`p^(sη)uᵢ₊₁=Dtᵢ₊₁`. Primitivity forces `η=0` and `tᵢ₊₁=1`; the remaining identity
`kᵢtᵢ=Lqᵢ−A`, together with `kᵢ∣DL(qᵢ−1)`, bounds `qᵢ` by the nonzero fixed residue
`Dtᵢ(A−L)`.

If `η≥(s−1)aᵢ`, the bounded left side is divisible by `qᵢ^(s−1)` and therefore vanishes for
large `qᵢ`. Valuation comparison forces `η=(s−1)aᵢ` and
`vₚ(D−L)=s(s−1)aᵢ`, again bounding `aᵢ`.

Thus both waits in every nondecreasing transition are effectively bounded. Positive integer
waits cannot decrease forever, so every wait is bounded. The recurrence and
`hᵢ∣DL(qᵢ−1)` then leave only finitely many reduced states. Functionality makes every infinite
orbit eventually periodic.

This theorem has been independently reconstructed but is not yet in Lean. It remains outside
the formal theorem boundary.

The surviving enemy is therefore precise: a coefficient-aligned orbit with unbounded reduced
denominators whose wait word evades every height-forced repeated factor. The endpoint reverse
matrix retains a spare factor of order `p^((s−1)a)`; the present content budgets do not pay for
it uniformly.

## Verification

The checked declarations are in
[`ReturnGuardEndpoint.lean`](../MatrixMortality/ReturnGuardEndpoint.lean),
[`ReturnGuardAdelic.lean`](../MatrixMortality/ReturnGuardAdelic.lean),
[`ReturnGuardPumping.lean`](../MatrixMortality/ReturnGuardPumping.lean), and
[`ReturnGuardExamples.lean`](../MatrixMortality/ReturnGuardExamples.lean). They compile under
the warning-free strict Lean gate. The full-project axiom snapshot owns their transitive axiom
boundary.
