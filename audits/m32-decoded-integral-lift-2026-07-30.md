# M₃(2) canonical decoded-integral lift

Date: 2026-07-30

## Claim

Fix guarded parameters with an integral presentation

```text
α=A/L,        ρ−α=D/L,        L≠0.
```

Every exact decoded rational step lifts canonically to one primitively reduced integral step.
Consequently every decoded execution lifts without changing its length, and every closed safe
exact-order quotient invariant is a finite certificate of physical immortality.

## Raw branch fraction

For a rational source `w=m/n` in canonical form and a legal wait `a`, denominator clearing gives

```text
Sₐ(w)=N/(p^(sa)T),
N=(A−Lpᵃ)m+Dn,
T=(A−L)m+Dn.
```

The source pair `(m,n)` is primitive because rational numerator and denominator are coprime.
Legality proves that `Sₐ(w)` is a p-adic unit.

Write the reduced target as `m′/n′`. Exact rational normalization supplies an integer `c` with

```text
N=c m′,        p^(sa)T=c n′.
```

The denominator `n′` is prime to `p`: otherwise the unit valuation would force `p` to divide
both `m′` and `n′`, contradicting their coprimality. Hence `p^(sa)` is coprime to `n′`, and
Euclid's lemma forces

```text
p^(sa) ∣ c.
```

Writing `c=p^(sa)g` yields

```text
N=p^(sa)g m′,        T=g n′,
```

which is exactly `PrimitiveIntegralStep`. The factor `p^(sa)` is not an optional
projective rescaling: branch legality forces it into the raw common reduction.

## Execution lift

The one-step construction is functional in the canonical pair map

```text
pair(w)=(num(w),den(w)).
```

Mapping a `Relation.ReachesIn` proof through this function therefore gives a primitive integral
execution with the same number of steps. No choice of signs, denominators, or intermediate
scalings remains.

This direction is sufficient for no-certificates:

```text
no primitive integral reset-to-terminal execution
⇒ no decoded rational reset-to-terminal execution
⇒ physical immortality.
```

The reverse implication is neither needed nor claimed. `PrimitiveIntegralStep` deliberately
forgets the p-adic branch guard and may admit abstract integral transitions which are not
decoded steps.

## Quotient certificates

Let an exact-order quotient invariant contain the canonical reset pair and exclude both the
cancellation state and the canonical terminal pair. The existing finite-automaton theorem
excludes primitive integral terminal execution; the lift now excludes decoded reachability and
the checked physical compiler turns this into immortality of the two 3×3 matrices.

The period-three parameters therefore admit two independent no-proofs:

1. the rational three-cycle invariant;
2. the four-ray quotient invariant `{1,4,6,10}⊂ℙ¹(𝔽₁₁)`.

The second proof now reaches the physical pair directly.

## Endpoint normalization hazard

The earlier drift-divisor theorem excluded primitive execution to the raw terminal pair

```text
(−D,A−L).
```

If this pair is not primitive, the statement may be vacuous: `PrimitiveIntegralStep` requires
its target pair to be coprime. The repaired physical theorem instead targets the canonical pair
of the rational terminal residual. It proves that canonical and raw pairs determine the same
finite projective point whenever `A−L` survives modulo the quotient prime.

Thus drift-divisor certificates require no global coprimality assumption on `(−D,A−L)`.

## Scope

The result closes certificate soundness, not certificate completeness. It does not prove that
every immortal guarded pair has a separating quotient, that every abstract integral execution
comes from a decoded orbit, or that cancellation histories form a finite nucleus. The live
problem is now entirely local-global: classify the parameter-divisor certificates, then decide
whether generic exact-order quotients or repeated swallowed factors control the complement.

## Lean artifacts

- `ReturnGuard.rat_denominator_not_dvd_of_isUnit`
- `ReturnGuard.primePower_dvd_common_of_unit_denominator`
- `ReturnGuard.residualStep_eq_integralRatio`
- `ReturnGuard.decodedStep_primitiveIntegralStep`
- `ReturnGuard.decodedExecution_primitiveIntegral`
- `ReturnGuard.not_decodedReachable_of_quotientInvariant`
- `ReturnGuard.not_physical_isMortal_of_quotientInvariant`
- `ReturnGuard.not_physical_isMortal_of_drift_divisor`
- `ReturnGuard.Examples.cycle_not_physical_isMortal_by_quotient`

The generic lift is in
[`ReturnGuardIntegralLift.lean`](../MatrixMortality/ReturnGuardIntegralLift.lean). The concrete
certificate is in
[`ReturnGuardQuotientExamples.lean`](../MatrixMortality/ReturnGuardQuotientExamples.lean).
