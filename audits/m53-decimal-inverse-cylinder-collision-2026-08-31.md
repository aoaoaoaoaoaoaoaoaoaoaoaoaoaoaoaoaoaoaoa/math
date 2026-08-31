# Decimal Setter Inverse-Cylinder Collision Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** backward carrier words have an exact unbounded decimal contraction, but two lawful
compiler-emitted blocks have identical first suffix cylinders

This audit concerns the generalized carrier after a surviving distinguished-reset entry. It
does not prove projective avoidance or settle `M₅(3)`.

## Exact Inverse Cylinder

Write a normalized multi-role block as

```text
τx−C=10^hExy,             C=μGV,             h=m−2≥1.
```

Solving for the current carrier gives the backward map

```text
Ψ(y)=C/(τ−10^hEy),                              (1)
```

where `E`, `τ`, `C`, and every live tail are decimal units. The denominator in (1) remains a
unit because it is a unit minus a positive-depth term. Direct subtraction gives

```text
Ψ(y)−C/τ=C10^hEy/(τ(τ−10^hEy)).                 (2)
```

Thus every unit tail maps to the exact cylinder

```text
ν₂(x−C/τ)=ν₅(x−C/τ)=h.                          (3)
```

Conversely, if a rational decimal unit `x` satisfies (3), then

```text
y=(τx−C)/(10^hEx)
```

is a decimal unit and `Ψ(y)=x`. Hence (3) is the exact rational image of the unit domain.

For two tails,

```text
Ψ(y)−Ψ(z)
 =C10^hE(y−z)/((τ−10^hEy)(τ−10^hEz)).           (4)
```

Equation (4) raises both valuations of `y−z` by exactly `h`. Induction over a bundled backward
word raises them by exactly the sum of its block shifts. This supplies a genuine unbounded
suffix metric.

## Rational Fixed-Point Seam

The stationary equation is

```text
10^hEx²−τx+C=0,
```

with discriminant `Δ=τ²−4·10^hEC`. A rational decimal-unit fixed point exists exactly when
there is a rational square root `s²=Δ` for which `τ+s` has joint shell `(h+1,h)`. The shell
condition records the simultaneous cancellation needed against `2·10^hE`; a rational square
discriminant alone is insufficient. This criterion classifies exact diagonal cycles but does
not by itself constrain finite reachable orbits.

## Physical Collision

Consider the distinct lawful blocks

```text
B_R=R_b R_c D_b,             B_D=D_b R_c D_b.
```

Both end in erasure. Rule and erasure phases carry the same upper `b`, so their complete upper
spellings coincide and have length

```text
m=2β+5,                       h=2β+3.             (5)
```

Let `H(body)` be the binary tag encoding of the compiler body. The lower spellings share the
suffix `R_cD_b`, of length

```text
L=|H(body)|+4.
```

The first lower prefixes have decimal codes `557` and `7`. Therefore

```text
V_R−V_D=(557−7)10^L=550·10^L,                   (6)
```

with exact shell `(L+1,L+2)`.

For a physical block, write

```text
z(P,V)=10μGV/(EP+GV).
```

When the upper code `P` is shared, subtraction cancels the quadratic `G` term:

```text
z(P,V_R)−z(P,V_D)
 =10μGEP(V_R−V_D)/((EP+GV_R)(EP+GV_D)).          (7)
```

The physical calibration makes `E`, `G`, `μ`, and `P` decimal units. Both blocks end in a
multi-role erasure, so both traces in (7) have exact shell `(1,1)`. Equations (6)–(7) give

```text
(ν₂,ν₅)(z(P,V_R)−z(P,V_D))=(L,L+1).             (8)
```

Neary's compiler guarantees `|H(body)|≥2β`, hence `L>h`. In either `2`-adic or `5`-adic
geometry, perturbing a center at depth strictly greater than `h` leaves its exact depth-`h`
sphere unchanged. Applying this at both primes proves

```text
ν₂(x−z(P,V_R))=ν₅(x−z(P,V_R))=h
  ↔
ν₂(x−z(P,V_D))=ν₅(x−z(P,V_D))=h.                (9)
```

The first forced suffix cylinder therefore cannot recover the leading phase of a physical
block.

## Boundary

Equation (9) refutes only first-cylinder itinerary decoding. It does not say that the two
Möbius branches are equal, that their complete composed addresses coincide, or that either
branch is reachable from the distinguished raw head. A successful closure must retain the
normalized tail inside the cylinder, compose deeper branch information, or prove that merging
these phase-hidden blocks preserves reachability.

## Verification

`inverseCarrier_mem_carrierCylinder` and
`existsUnique_inverseCarrier_unit_iff_carrierCylinder` prove (2)–(3), their converse, and the
uniqueness of the decoded tail for a fixed branch.
`BackwardBlock.pullbackWord_sub_hasDecimalShell` proves the summed version of (4).
`hiddenBlocks_upper_length`, `hiddenBlocks_lowerCode_sub`,
`physicalCarrierCenter_sameUpper_sub_hasDecimalShell`, and
`emittedHiddenBlocks_firstCylinder_collision` prove (5)–(9) under the physical calibration.
The narrow module build, namespace lint, language-server diagnostics, and selected axiom audit
pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterSuffix.lean`](../MatrixMortality/DecimalSetterSuffix.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-o20-decimal-first-cylinder-collision)
- [`m53-decimal-bounded-suffix-cycles-2026-08-30.md`](m53-decimal-bounded-suffix-cycles-2026-08-30.md)
