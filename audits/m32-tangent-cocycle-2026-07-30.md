# M₃(2) normalized tangent-cocycle audit

**Date:** 2026-07-30  
**Status:** Lean-checked structure theorem; `M₃(2)` remains open

## Question

The primitive-cancellation blow-up leaves one unrestricted datum at equal depth:

```text
[T₀+C₀:T₀].
```

The experiment asked whether this datum admits an orbit-specific scalar descent, or whether
normalization recreates a full recurrence on the exceptional divisor.

## Coordinate

Let a decoded step of wait `a` end at the primitive pair `(m,n)`. Put

```text
P = p^(sa),
v = (n, Pm−n).
```

The first coordinate is the preceding terminal term after primitive division. The second is the
preceding cyclotomic displacement after the same division. Their common factor has therefore
already been removed.

If `(m,n)` is primitive and `n` is coprime to `P`, then `v` is primitive:

```text
gcd(n,Pm−n)=gcd(n,Pm)=1.
```

The base-coprimality premise is automatic for canonical decoded residuals, whose denominators
are prime to `p`.

## Exact cocycle

Suppose the next wait is `b`, its raw output reduces by the scalar `g`, and `v′` is the next
tangent pair in the chart `p^(sb)`. Direct elimination gives

```text
M(P,b)v = Pg v′,
```

where

```text
M(P,b) =
  [ A−L+DP      A−L       ]
  [ L(1−pᵇ)     L(1−pᵇ)   ].
```

This is not a congruence or a projective approximation. It is an equality over `ℤ`, and it
retains the complete normalization scalar.

The two rows have transparent meanings. The first is `P` times the next terminal defect. The
second is `P` times the next cyclotomic displacement. Thus a second collision is a common
factor of the two entries of `M(P,b)v`.

## Recursive determinant support

The determinant is

```text
det M(P,b)=DLP(1−pᵇ).
```

Since `v` is primitive, every scalar removed after tangent transport divides this determinant.
Away from primes dividing `DLP`, every new cancellation factor therefore divides `pᵇ−1`.

Primitive cancellation has reproduced the original dichotomy on the exceptional divisor:

```text
fixed parameter support  or  next cyclotomic support.
```

It has not collapsed the dynamics to a bounded correction state.

Modulo a cyclotomic prime, `pᵇ=1`, and the bottom row vanishes. The tangent is swallowed again
exactly on the moving kernel line

```text
(A−L+DP)T + (A−L)C = 0.
```

The dependence on `P=p^(sa)` couples consecutive waits. A universality construction would have
to steer the tangent through these lines; a decision argument must prove that canonical reset
execution cannot do so at unbounded novel depth.

## Canonical tangent cycle

The existing rational period-three guard has primitive residual cycle

```text
1/1 ─1→ 5/17 ─2→ 43/283 ─3→ 1/1.
```

Its tangent coordinates are

```text
v₀=(17,28),
v₁=(283,3200),
v₂=(1,728).
```

Lean checks

```text
M(9,2)v₀   = −252 v₁,
M(81,3)v₁  = −278640 v₂,
M(729,1)v₂ = −116640 v₀.
```

All scalars are nonzero. This is a genuine projective tangent three-cycle carried by the
canonical reset orbit. Consequently no scalar height can strictly decrease on every tangent
step.

The counterexample is sharply scoped: the primitive-reduction factors `28`, `3440`, and `160`
all divide the fixed parameter product `DL`. It does not refute a descent theorem after fixed
support has been normalized away.

## Adjudication

The proposed direct scalar tangent-depth descent is rejected in its unnormalized form. The
experiment nevertheless exposes the correct next object: the **fixed-support-normalized tangent
cocycle**.

A successful decidability proof must:

1. quotient or canonically normalize valuations at the finite prime set dividing `DL`;
2. retain the primitive tangent pair rather than one scalar depth;
3. bound the remaining novel cyclotomic normalization along the canonical reset orbit.

A successful universality proof must instead construct one rational reset orbit whose tangent
vectors meet infinitely many moving kernel lines with unbounded swallowed depth.

## Lean boundary

The following declarations are checked without project axioms:

- `ReturnGuard.cancellationTangent`;
- `ReturnGuard.tangentTransfer_mulVec`;
- `ReturnGuard.tangentTransfer_det`;
- `ReturnGuard.cancellationTangent_of_reducedIntegralStep`;
- `ReturnGuard.tangentTransfer_of_consecutive_reduction`;
- `ReturnGuard.cancellationTangent_isCoprime_of_base`;
- `ReturnGuard.tangent_reductionFactor_dvd_support`;
- `ReturnGuard.tangent_novelDivisor_dvd_cyclotomic`;
- `ReturnGuard.tangentTransfer_mod_eq_zero_iff_terminal`;
- `ReturnGuard.Examples.cycle_tangent_step_zero`;
- `ReturnGuard.Examples.cycle_tangent_step_one`;
- `ReturnGuard.Examples.cycle_tangent_step_two`.

The proofs are in
[`ReturnGuardTangent.lean`](../MatrixMortality/ReturnGuardTangent.lean) and
[`ReturnGuardTangentExamples.lean`](../MatrixMortality/ReturnGuardTangentExamples.lean).
