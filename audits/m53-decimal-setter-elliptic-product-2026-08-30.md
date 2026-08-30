# Decimal Setter Elliptic-Product Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** two strictly hyperbolic decimal setter blocks have an elliptic product; blockwise
hyperbolicity cannot prove projective avoidance

Nothing here supplies a false pole orbit or proves `M₅(3)`.

## J-Fraction Product

Write a decimal setter block as

```text
F_z(t)=u_z+v_z−v_z/t,       u_z,v_z>0,
J_z=[[u_z+v_z,−v_z],[1,0]].
```

Its discriminant is `(u_z+v_z)²−4v_z`. For two blocks, direct multiplication gives

```text
disc(J₂J₁)=((u₁+v₁)(u₂+v₂)−v₁−v₂)²−4v₁v₂.       (1)
```

Individual positivity of the first discriminant does not control (1).

## Emitted-Body Pair

Specialize to `β=10`, radix ten, and digits `0 ↦ 7`, `1 ↦ 5`. Put

```text
ρ=10¹⁰,
μ=(52ρ−7)/9,
L=(502ρ−7)/(9(2ρ−7)),
C=L/μ.
```

Let the low block be the single erasure `D_c`. Let the high block begin with `R_c`, continue
only with `b`-letter roles, and have lower-minus-upper length defect `11`. The two checked
compiler bodies begin with `b`, so the normalized lower decimal word of the high block begins

```text
55 7¹⁰ 5.
```

All later digits are `5` or `7`. Consequently its normalized lower value `f` satisfies

```text
5577777777775 / 10¹³
  ≤ f
  ≤ 5577777777775 / 10¹³ + 7/(9·10¹³).             (2)
```

The upper word is `cbⁿ`. Its normalized coefficient is trapped between the first iterate and
the fixed point of

```text
T_b(x)=1+(5r+x)/10¹²,       r=10ρ/μ.
```

Equations (2) and the fixed-point bound imply the exact rational boxes

```text
0.9653846153 ≤ u_high,u_low ≤ 0.9653846155,
26.92350428  ≤ v_high       ≤ 26.92350429,
3.378846155·10⁻¹⁰ ≤ v_low  ≤ 3.378846156·10⁻¹⁰.   (3)
```

The two period-one compiler checkpoints instantiate the defect exactly:

| body | length | `b` count | high block after `R_c` |
| --- | ---: | ---: | --- |
| emitted body 0 | 13,959 | 7,026 | `R_b¹⁰D_b⁸²⁸⁶` |
| emitted body 1 | 14,949 | 7,521 | `R_b¹⁰D_b⁸⁸⁷¹` |

For body 0, for example,

```text
91247−10·9−8286·11=11.
```

The second identity is `97682−10·9−8871·11=11`. Thus both blocks have the coefficients
covered by (3).

## Exact Sign

Throughout (3), both individual discriminants are positive. The trace in (1) obeys

```text
0 < (u_high+v_high)(u_low+v_low)−v_high−v_low < 10⁻⁷,
```

whereas

```text
4v_highv_low > 10⁻¹⁴.
```

Therefore `disc(J_low J_high)<0`. Lean proves the coefficient-box theorem, derives (2) from a
finite decimal tail bounded by `7/9`, proves the `T_b` invariant interval, and instantiates the
elliptic product as
`SetterJFraction.leadingB_elliptic_pair`.

The smallest concrete checkpoint witness is shorter. For body `bcbbbbbbc`, the pair

```text
high = R_cD_b⁷,       low = D_c
```

has total role length nine. Its exact trace ratio is approximately
`2.268416898×10⁻⁹` of the parabolic threshold `4v_highv_low`; the Lean interval theorem covers
it without relying on this decimal approximation.

## Boundary

The elliptic product refutes any inference from blockwise hyperbolicity to semigroup uniform
hyperbolicity or a common proper convex cone. It does not imply a rational pole hit. An exact
bidirectional search over the two-letter block alphabet `{high,low}`, both reset values, and
both pole targets found no false-pole intersection through 36 projective maps. This bounded
result is diagnostic only.

The surviving decimal route is arithmetic. In homogeneous coordinates, with

```text
E=9(2ρ−7),       G=502ρ−7,
```

one block updates

```text
X'=(EP+GV)X−GVY,       Y'=Eμ10^mX.
```

The next proof must use the joint `2`/`5`-adic carry or an equivalent exact suffix invariant;
real cone subdivision is closed.
