# M₃(2) center/reset parameter-plane audit

**Date:** 2026-07-30  
**Status:** Lean-checked first-order cocycle and exact guard escape; anisotropic lifting open

## Question

Does the anti-Hensel collision found under fixed-reset center lifting persist when both guard
parameters vary?

## Exact parameter plane

Changing center by `ε` and reset by `η` changes drift by `η−ε`. For a homogeneous residual
source `(m,n)` at wait `a`, direct matrix multiplication gives

```text
Δtransfer = (ε(m−n)+ηn)·(1,p^(sa)).
```

The residual displacement remains rank one in state space, but its coefficient is a linear form
on a two-dimensional parameter space. The earlier center-only tangent is the slice `η=0`.

## Affine escape

Write one old annular condition and the new incidence as

```text
oldValue + oldGradient·digit = oldTarget,
newValue + newGradient·digit = 0.
```

If the gradient determinant is nonzero, Lean verifies the explicit Cramer-rule digit solving
both equations. Taking `oldTarget=1` imposes the new incidence while discharging the active old
annulus to a unit. If a later refinement changes that old affine value by a positive-valuation
quantity, the unit-plus-positive law preserves the old shell. Historical shells therefore do
not accumulate as independent first-order constraints once discharged.

## Guard-specific transport

Let `g=(g₀,g₁)` be the center/reset sensitivity of a ready state. One legal update has the form

```text
g' = (1−H,H) − Cg,
```

where `H` is the legal payload and `C` is the derivative contributed by ready-tail extraction.
The exterior product is

```text
g∧g' = H(g₀+g₁)−g₁.
```

The singular transported term `−Cg` is parallel to `g` and cancels. This gives a
fixed-dimensional first-order cocycle: transversality is decided by one scalar, independently
of the size of the transported derivative.

This closes the live experiment's first-order state question. The unresolved issue is not an
ever-growing list of annuli. It is whether the Cramer-rule digit lies in the anisotropic
center/reset refinement lattice that keeps every discharged shell invisible.

## Exact guard witness

The fixed-reset family

```text
p=3, s=2, α=998, ρ=−168
```

has legal waits `1,3` and no third decoded step. Keeping `α=998` and changing only reset by
`3⁸` gives

```text
ρ=6393
```

and the exact legal prefix `1,3,1`. Lean checks all three ready conditions and residual values.
Thus the dead center cylinder is codimension one: reset motion at the correct precision
strictly extends it.

## Long-prefix computation

The exact-arithmetic alternating ladder previously died at collision twenty-six under
center-only refinement. Holding its collision-twenty-five center digit fixed and perturbing
reset at the tested anisotropic scale produced a legal collision twenty-six; one witness uses
reset digit six at scale `centerModulus·3¹⁰`.

This is computational evidence, not a Lean theorem. It shows that the small exact witness is
not isolated and selects the next experiment: derive the general precision law rather than
searching more digits.

## Lean boundary

The checked declarations are:

- `ReturnGuard.integralResidualTransfer_centerReset_add_mulVec`;
- `ReturnGuard.integralResidualTransfer_centerReset_factor`;
- `ReturnGuard.planeSolveDigit_spec`;
- `ReturnGuard.affinePlaneValue_isUnit_add_of_positive`;
- `ReturnGuard.readyLegalValue_reset_hasDerivAt`;
- `ReturnGuard.planeCross_parameterGradientStep`;
- `ReturnGuard.exists_planeDigit_hits_parameterGradientStep_and_preserves`;
- `ReturnGuard.Examples.resetEscape_threeStepPrefix`;
- `ReturnGuard.Examples.resetEscape_strictly_extends_deadCenter`.

They live in
[`ReturnGuardParameterPlane.lean`](../MatrixMortality/ReturnGuardParameterPlane.lean) and
[`ReturnGuardParameterPlaneExamples.lean`](../MatrixMortality/ReturnGuardParameterPlaneExamples.lean).

## Remaining obligation

Determine the exact valuation transport of both sensitivity coordinates and of
`H(g₀+g₁)−g₁`. A successful lifting theorem must prove:

1. the transverse digit pair is integral at the next center/reset scales;
2. its higher-order error is positive at every discharged shell;
3. the next normalized annulus is a unit;
4. these properties iterate without increasing the jet order.

Failure of any item should be isolated as an exact higher-jet obstruction rather than reported
as a search miss.
