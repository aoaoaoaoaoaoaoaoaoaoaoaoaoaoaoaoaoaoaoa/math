# M₃(2) fixed-support localization audit

**Date:** 2026-07-30  
**Status:** Lean-checked negative experiment; `M₃(2)` remains open

## Question

The normalized tangent cocycle has determinant

```text
det M(P,b)=DLP(1−pᵇ).
```

The experiment asked whether removing the fixed factor `D·L·p` leaves an effectively finite
state space. The answer is no in the uniform primitive-input formulation.

## Canonical normalization

Coordinatewise removal of fixed prime powers does not respect addition and therefore does not
define a recurrence. The canonical multiplicative normalization is the localization

```text
ℤ[1/(D·L·p)].
```

In any commutative localization away from `D·L·p`, the images of `D`, `L`, `p`, and every
`P=p^(sa)` are units. Lean proves

```text
M(P,b) is invertible  ↔  1−pᵇ is a unit.
```

Thus localization does exactly one legitimate thing: it removes fixed support and no more.
Every residual singularity is cyclotomic.

The proof is not specific to the integers. The determinant theorem is stated over an arbitrary
commutative ring, and the localization theorem over any commutative `ℤ`-algebra satisfying the
appropriate universal property.

## A specialization detector

The reusable local principle is:

> If a ring map sends the inverted element to a unit but sends another element to a nonunit,
> then the latter element remains a nonunit in the away localization.

The proof factors the specialization through the localization. Were the localized element a
unit, its image under every such factorization would be a unit.

This gives finite-quotient certificates for distinctions inside the localization. In
particular, after localizing `ℤ` away from five, the powers

```text
3^i, 3^j
```

are nonassociated for `i<j`. Specialize to `ℤ/(3^(i+1))`. Five is invertible in that quotient,
so the map descends from `ℤ[1/5]`; `3^j` vanishes while `3^i` does not. Associated elements
cannot have different zero behavior under a ring homomorphism.

The localized state space therefore contains the strict infinite tower

```text
1, 3, 3², 3³, …
```

up to units.

## Collision witness

The existing exact cancellation construction uses the single guarded recurrence

```text
(p,s,A,D,L)=(5,2,29,1,1).
```

For every `d>0`, it supplies a primitive integral input and wait whose common output factor has
exact `3`-adic depth `d`. The present development appends the localization certificate:

```text
3^d is not a unit in ℤ[1/5].
```

Hence arbitrary novel depth survives the complete fixed-support normalization. This is stronger
than observing one bad residue: no uniform finite quotient can identify the entire depth axis
through multiplication by fixed-support units.

## Adjudication

The hypothesis that fixed-support localization alone yields a finite core is rejected.

The obstruction is sharply quantified. It ranges over freely chosen primitive inputs to one
fixed recurrence. It does **not** prove that the canonical reset orbit of one mortality instance
realizes unbounded novel depth. Accordingly:

- a uniform decidability proof over the localized primitive state space is dead;
- an orbit-specific height or product formula remains live;
- a universality proof must steer one reset orbit through the strict localized tower.

The next experiment should compare the product of novel swallowed factors along a reset
execution with the primitive tangent height. The crucial issue is whether the recurrence can
pay for repeated new cyclotomic depth without a commensurate, effectively bounded height
increase.

## Lean boundary

The following declarations are checked without project axioms:

- `ReturnGuard.tangentTransfer_det_associated_cyclotomic`;
- `ReturnGuard.tangentTransfer_isUnit_iff_cyclotomic`;
- `ReturnGuard.away_algebraMap_not_isUnit_of_map`;
- `ReturnGuard.tangentTransfer_localized_isUnit_iff`;
- `ReturnGuard.awayFive_three_not_isUnit`;
- `ReturnGuard.awayFive_three_pow_not_isUnit`;
- `ReturnGuard.awayFive_three_pow_not_associated_of_lt`;
- `ReturnGuard.exists_localized_nonunit_three_cancellationDepth`.

The proofs are in
[`ReturnGuardTangent.lean`](../MatrixMortality/ReturnGuardTangent.lean) and
[`ReturnGuardLocalization.lean`](../MatrixMortality/ReturnGuardLocalization.lean).
