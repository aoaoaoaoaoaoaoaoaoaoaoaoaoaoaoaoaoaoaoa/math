# M₃(2) anisotropic parameter-lattice audit

**Date:** 2026-07-30  
**Status:** Lean-checked valuation transport and exact weighted cylinder

## Question

Does the two-parameter escape of the center/reset plane live in an iteration-ready integral
lattice, or does p-adic conditioning reintroduce an obstruction despite rational
transversality?

## Mass coordinates

For center/reset sensitivity `g=(g₀,g₁)`, define

```text
u = g₀+g₁,      r = g₁.
```

The legal cocycle

```text
g' = (1−H,H)−Cg
```

then gives

```text
u' = 1−Cu,      r' = H−Cr.
```

At every positive wait `a`, positive depth `s`, unit drift and unit tail, Lean proves that `H`
is a unit and `v_p(C)=−sa`. If `u` and `r` have one common nonpositive valuation `v`, both
outputs have exact valuation `v−sa`. Their equality of scales persists, while their absolute
magnitude grows by the singular factor `p^(−sa)`.

## Projective freezing

Put `θ=r/u`. Exact rational algebra gives

```text
θ'−θ = (g∧g')/(u'u),
g∧g' = u(H−θ).
```

For a transverse step this yields

```text
v_p(θ'−θ)=v_p(H−θ)−v+sa.
```

Both `H` and `θ` are units, so their nonzero difference has nonnegative valuation. Hence

```text
v_p(θ'−θ) ≥ sa−v > 0.
```

The two rational sensitivities remain linearly independent, but their projective directions
become increasingly close. A fixed equal-precision center/reset lattice therefore cannot
provide a uniformly unimodular Cramer basis. This is an exact obstruction to naïve iteration,
not a failure of a bounded digit search.

## Exact weighted cylinder

The reset escape at `(center,reset)=(998,6393)` belongs to the two-dimensional family

```text
center = 998 + 3^8 c,
reset  = 6393 + 3^11 r,       c,r∈ℤ.
```

Lean proves that every such pair satisfies the guard envelope and has three decoded steps with
waits

```text
1, 3, 1.
```

The proof is uniform in both integer digits. Each required numerator and denominator is reduced
modulo three to an explicit unit, and all residual identities are checked over `ℚ`. At
`c=r=0`, the family is definitionally the previously checked reset-only escape.

The cylinder shows that anisotropy is also constructive. Unequal center/reset scales preserve
the old prefix throughout an entire congruence neighborhood; the live question is how those
scales evolve after further collisions.

## Lean boundary

The checked declarations are:

- `ReturnGuard.legalPayload_isUnit`;
- `ReturnGuard.sensitivityMultiplier_hasValue`;
- `ReturnGuard.parameterGradientMass_step_hasValue`;
- `ReturnGuard.parameterGradientStep_one_hasValue`;
- `ReturnGuard.parameterGradientRay_step_sub`;
- `ReturnGuard.planeCross_parameterGradientStep_eq_mass_mul_rayDefect`;
- `ReturnGuard.parameterGradientRay_step_sub_hasValue`;
- `ReturnGuard.parameterGradientRay_step_valuation_lower_bound`;
- `ReturnGuard.parameterGradientRay_step_isPositive`;
- `ReturnGuard.Examples.weightedEscape_threeStepPrefix`;
- `ReturnGuard.Examples.weightedEscape_zero_eq_resetEscape`.

They live in
[`ReturnGuardParameterLattice.lean`](../MatrixMortality/ReturnGuardParameterLattice.lean) and
[`ReturnGuardParameterLatticeExamples.lean`](../MatrixMortality/ReturnGuardParameterLatticeExamples.lean).

## Remaining obligation

Derive the multi-step valuation of the affine escape digit itself. A decisive continuation must
do one of two things:

1. renormalize the frozen ray into an integral weighted or higher-jet cocycle and construct
   arbitrary finite compatible prefixes; or
2. prove that compatible digits determine a strictly profinite inverse limit with no rational
   parameter pair, yielding an effective obstruction to infinite rational lifts.

The present theorem neither asserts arbitrary-prefix synthesis nor a rational infinite orbit.
