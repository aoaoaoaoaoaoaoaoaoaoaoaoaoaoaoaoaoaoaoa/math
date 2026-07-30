# M₃(2) center-drift parameter-lifting audit

**Date:** 2026-07-30  
**Status:** Lean-checked local synthesis law and five-step certificate; `M₃(2)` remains open

## Question

Can the next cyclotomic moving-kernel collision be imposed without destroying the reduction
factor already present at the current canonical step?

## Exact perturbation law

Fix a homogeneous source `(m,n)` and wait `a`. Keep the reset fixed while changing the integral
center numerator by `ε`; the drift numerator changes by `−ε`. Direct matrix algebra gives

```text
M(A+ε,D−ε)·(m,n)
  = M(A,D)·(m,n) + ε(m−n)(1,p^(sa)).
```

The parameter dependence is therefore one-dimensional. If

```text
M(A,D)·(m,n)=q·v
```

and `ε=q t`, then

```text
M(A+qt,D−qt)·(m,n)
  = q·(v+t(m−n)(1,p^(sa))).
```

The old factor `q` survives identically. Over a field, an observer `ℓ` with

```text
ℓ·(m−n)(1,p^(sa)) ≠ 0
```

selects exactly one digit

```text
t = −(ℓ·v)/(ℓ·(m−n)(1,p^(sa)))
```

whose reduced exit lies in `ker ℓ`. This is the local algebra required by a CRT/Hensel
collision-prefix construction.

## Five checked collisions

The guard

```text
(p,s,α,ρ)=(3,2,23278364,52569)
```

has canonical residual waits

```text
4,2,2,1,3.
```

Lean checks every ready-state valuation, every decoded rational transition, and every primitive
integral lift. The common reduction factors are

```text
8,2,20,2,13.
```

The factor five in `20=5·4` belongs to the fixed drift support. Removing fixed support leaves

```text
8,2,4,2,13,
```

five consecutive nonunit novel reductions.

## Computational extension and its failure

This section is superseded by the anti-Hensel audit below. Exact rational arithmetic,
independent of Lean, extends the prescribed parameter classes uniquely through collision
twenty-five. After the checked prefix, the waits and selected factors repeat the pattern

```text
1/2, 3/13.
```

A wait-one extension adds `3²`-adic precision. A wait-three, factor-thirteen extension adds
`13·3⁶`. At collision twenty-six, exhaustive exact evaluation of the relevant next digit
classes finds no extension. The apparent induction was false.

The failure is structural. Readiness requires an exact valuation, hence a nonzero normalized
annular digit. The unique parameter digit imposing the new incidence may annihilate that old
digit. [`m32-anti-hensel-prefix-obstruction-2026-07-30.md`](m32-anti-hensel-prefix-obstruction-2026-07-30.md)
records the formal compatibility criterion and a small all-cylinder guard obstruction.

## Adjudication

The local moving-kernel equation is solved whenever the tangent is visible, but visibility does
not imply prefix stability. The remaining problem is to transport every active annular
coefficient together with the incidence observer. An adaptive schedule may avoid the
compatibility zero locus; the fixed alternating schedule does not.

## Lean boundary

The following declarations are checked without project axioms:

- `ReturnGuard.integralResidualTransfer_centerDrift_add_mulVec`;
- `ReturnGuard.integralResidualTransfer_centerDrift_factor`;
- `ReturnGuard.existsUnique_incidenceDigit`;
- `ReturnGuard.existsUnique_centerDriftDigit`;
- `ReturnGuard.Examples.fiveCollision_decodedSteps`;
- `ReturnGuard.Examples.fiveCollision_primitiveSteps`;
- `ReturnGuard.Examples.fiveCollision_novelFactors`.

The generic laws are in
[`ReturnGuardParameterLift.lean`](../MatrixMortality/ReturnGuardParameterLift.lean); the exact
trajectory is in
[`ReturnGuardParameterLiftExamples.lean`](../MatrixMortality/ReturnGuardParameterLiftExamples.lean).
