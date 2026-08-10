# The uniform-fiber semigroup ceiling

Date: 2026-08-08

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

No full-fiber finite-semigroup entropy proof of Zargar's pointwise-functional type can establish
the half-frequency theorem at homogeneous set weight `t>16/27`. At uniform weight `t=1`,
every such proof is bounded by the same point-mass obstruction that yields the golden-ratio constant

```text
(3−√5)/2.
```

The obstruction is independent of the multiplication table. It follows only from the Boolean
projection, the two fiber sizes, and maximal entropy within each fiber. Thus inventing a more
ingenious finite semigroup cannot improve the universal uniform bound through a functional that
must be positive on every fixed-mean conditional law, unless the lift abandons uniform full
fibers, independent multiplication, or the coordinatewise entropy decomposition.

## Setup

Let `S` be a finite semigroup with a surjective homomorphism

```text
π:S→{0,1},
π(ab)=π(a)π(b).
```

Write

```text
S₀=π⁻¹(0),   |S₀|=k,
S₁=π⁻¹(1),   |S₁|=m,
t=m/k.
```

For `0≤x≤1`, let `Pₓ` be the fiber-uniform law assigning total mass `x` to `S₀` and
`1−x` to `S₁`. Its entropy is

```text
h(x)=B(x)+x log k+(1−x)log m,
```

where `B(x)=−x log x−(1−x)log(1−x)`.

This is the one-coordinate law forced by a uniform full-fiber lift of an
intersection-closed family. The induced base-family weight is proportional to `t^|A|`.

## Point-Mass Ceiling

Let `X,Y` be independent with law `Pₓ`, and put

```text
z=Pr[π(XY)=0]=1−(1−x)^2=2x−x^2.
```

Whatever the multiplication table, a random variable supported on `S` with base-zero mass
`z` has entropy at most the fiber-uniform value `h(z)`. Therefore

```text
H(XY)−H(X)
  ≤ h(z)−h(x)
  = B(2x−x^2)−B(x)+x(1−x)log(k/m).
```

In the measure-functional language, this bounds the entropy increment at the admissible
point-mass conditional law `μ=δₓ`. Any theorem requiring strictly positive increment for every
mean `0<x<1/2` must satisfy the limiting necessary condition at `x↑1/2`:

```text
0 ≤ B(3/4)−B(1/2)+(1/4)log(k/m).
```

Since

```text
B(3/4)−B(1/2)=log 2−(3/4)log 3,
```

the condition is equivalent to

```text
log(k/m) ≥ log(27/16),
k/m ≥ 27/16,
t=m/k ≤ 16/27.
```

This proves the half-frequency ceiling.

## Uniform Consequence

At uniform base weight, `k=m`, and the fiber terms cancel. The best possible point-mass
increment is

```text
B(2x−x^2)−B(x).
```

For `0<x<1/2`, its nontrivial zero occurs when binary-entropy symmetry gives

```text
2x−x^2=1−x.
```

Thus

```text
x^2−3x+1=0,
x=(3−√5)/2.
```

Above this value the entropy upper bound is already negative. Hence no multiplication table in
the stated lift architecture can improve the golden-ratio abundance constant at uniform weight
through a pointwise-positive fixed-mean functional. This recovers the known entropy barrier
without using approximate union closure and shows that it survives arbitrary finite-semigroup
label engineering in that proof schema.

## Relation To The Binary Theorem

The audited `k=2,m=1` theorem operates at `t=1/2`, safely below the necessary ceiling
`16/27≈0.592592`. Its sharp lower bound shows that one concrete semigroup works throughout
`0<x<1/2`; the present result shows why this success cannot be continued anywhere near
`t=1` inside the same architecture.

An attack may still use the binary theorem as an endpoint and exploit closure while tilting the
base family. It should not spend effort searching finite multiplication tables for a direct
uniform-weight improvement.

## Evidence Boundary

The ceiling is an audited information-theoretic obstruction. It covers full-fiber lifts whose
conditional label law is uniform inside two fixed fibers and whose proof compares an independent
semigroup product to the original coordinate entropy. It does not exclude nonuniform fibers,
history-dependent label laws, multi-coordinate products, dependent couplings, or arguments that
use more than coordinatewise Shannon entropy.

## Sources

- [Zargar 2023](../references/zargar-2023-union-closed-nonuniform-distributions.md),
  full-fiber semigroup lift and entropy-functional architecture.
- [Alweiss, Huang, and Sellke 2024](../references/alweiss-huang-sellke-2024-improved-lower-bound-frankl-journal.md),
  peer-reviewed golden-ratio benchmark.
