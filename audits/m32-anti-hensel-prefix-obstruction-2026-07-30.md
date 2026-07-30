# M₃(2) annular parameter-lifting audit

**Date:** 2026-07-30  
**Status:** Lean-checked sensitivity law, compatibility criterion, and dead parameter cylinder;
`M₃(2)` remains open

## Question

Does a visible center derivative suffice to extend a prescribed legal collision prefix by one
more parameter digit?

## Sensitivity transport

Keep the reset fixed and vary the center. At a ready state of wait `a`, let the current state
sensitivity have negative `p`-adic value `v`. Differentiating the ready-tail extraction and the
legal affine update gives a total sensitivity recurrence. Its transported term has value

```text
v − s a,
```

while every explicit term is integral. Unequal-valuation addition therefore proves that the
next sensitivity has exactly value `v−sa`. Once sensitivity is negative, first-order
visibility persists and grows at the expected depth.

## Annular compatibility

Readiness is not a root equation. It asserts divisibility to a prescribed depth and nondivisibility
at the next digit. After normalization, preserve one old shell and impose one new incidence:

```text
oldValue + t oldSlope ≠ 0,
newValue + t newSlope = 0.
```

If `newSlope≠0`, the new incidence has the unique solution

```text
t = −newValue/newSlope.
```

Substitution into the old coefficient gives

```text
(oldValue·newSlope − oldSlope·newValue)/newSlope.
```

Hence an extension exists exactly when the cross-determinant

```text
oldValue·newSlope − oldSlope·newValue
```

is nonzero. Vanishing is a complete anti-Hensel obstruction: the unique digit solving the new
incidence destroys the old exact shell.

## Exact dead cylinder

For every integer `d`, take

```text
p=3, s=2, ρ=−168, α=−460+729d.
```

Lean proves that every parameter in this entire center congruence cylinder has the decoded
wait prefix `1,3`. The state after those two steps is a `3`-adic unit for every `d`. A decoded
step requires a positive state valuation, so no third step exists anywhere in the cylinder.

This is not a finite sample and does not depend on large coefficients from the collision-ladder
search. It is an exact family theorem.

## Alternating collision computation

The prescribed `p=3`, `s=2`, `ρ=52569` center-lifting branch alternates waits and requested
novel factors

```text
1/2, 3/13.
```

Exact rational branch enumeration found one compatible digit at every requested extension
through collision twenty-five. At collision twenty-six, all relevant wait-one digit classes
fail. Refining the preceding center class by one further `3`-adic digit leaves only two classes
with the required collision-twenty-five annulus; neither reaches the next ready shell.

This bounded computation is not a Lean theorem and is not used as one. It adjudicates the
proposed fixed-schedule induction: the branch terminates, and the failure has the form predicted
by the formal compatibility determinant.

## Consequence

The implication

```text
visible next observer  ⇒  compatible prefix extension
```

is false. Parameter synthesis must carry a vector of active annular coefficients, not only one
state derivative. The next research object is their compatibility cocycle under a legal guard
step.

This does not exclude:

- another wait/factor schedule avoiding the determinant zero locus;
- arbitrarily long prefixes with schedules chosen adaptively;
- an infinite rational or profinite orbit in another parameter family;
- a decidability theorem derived from eventual incompatibility.

## Lean boundary

The checked declarations are:

- `ReturnGuard.readyLegalValue_hasDerivAt`;
- `ReturnGuard.parameterSensitivityStep_hasValue`;
- `ReturnGuard.exists_incidenceDigit_and_preserves_iff`;
- `ReturnGuard.no_incidenceDigit_preserves_of_liftCompatibility_eq_zero`;
- `ReturnGuard.Examples.deadLift_twoStepPrefix`;
- `ReturnGuard.Examples.deadLift_terminalState_isUnit`;
- `ReturnGuard.Examples.deadLift_noThirdStep`.

They live in
[`ReturnGuardSensitivity.lean`](../MatrixMortality/ReturnGuardSensitivity.lean),
[`ReturnGuardAntiHensel.lean`](../MatrixMortality/ReturnGuardAntiHensel.lean), and
[`ReturnGuardAntiHenselExamples.lean`](../MatrixMortality/ReturnGuardAntiHenselExamples.lean).
