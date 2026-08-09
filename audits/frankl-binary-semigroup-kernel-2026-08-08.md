# The binary semigroup kernel at inverse temperature `log 2`

Date: 2026-08-08

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

Zargar's nonuniform entropy argument extends to the omitted case `k=2`, `m=1`.
More precisely, his entropy-increment functional satisfies the sharp inequality

```text
F₂,₁(μ) ≥ φ(1−2φ) log 2 > 0
```

for every probability measure `μ` on `[0,1]` of mean `0<φ<1/2`. Equality in the
displayed lower bound is attained by the endpoint Bernoulli measure
`(1−φ)δ₀+φδ₁`.

Consequently, every finite intersection-closed family with at least two members has a
coordinate omitted from **strictly more** than half of its mass under weights `2^(−|A|)`.
Dually, every nontrivial finite union-closed family has a coordinate contained in strictly
more than half of its mass under weights `2^|A|`.

This is a weighted class theorem, not an improvement to the universal uniform abundance
constant. Its operational value is that a homogeneous-tilt attack now has a rigorous sharp
endpoint at weight `1/2`.

## The Functional

Put `H(u)=−u log u`, with `H(0)=0`, and let

```text
B(x) = H(x)+H(1−x),
L    = log 2.
```

Specializing Zargar's kernels to `k=2`, `m=1` gives

```text
h(x) = B(x)+xL,

g(x,y) = H((1−x)(1−y))
         + H((x+y)/2)
         + H((x+y−2xy)/2).
```

For a probability measure `μ` of mean `φ`, define

```text
F(μ) = ∬ g(x,y) μ(dx)μ(dy) − ∫ h(x) μ(dx).
```

This is exactly Zargar's `F₂,₁`. The only part nonlinear in `μ` is the double
integral.

## Concavity

Let `ν` be a finite signed measure on `[0,1]` with

```text
∫1 dν = 0,   ∫x dν = 0.
```

It suffices to prove

```text
Q(ν) = ∬ g(x,y) ν(dx)ν(dy) ≤ 0.
```

The three summands of `g` can be treated separately.

For `a=(1−x)(1−y)`, the identity

```text
H(a) = −(1−x)(1−y)(log(1−x)+log(1−y))
```

shows that its quadratic form vanishes: each separated term contains the factor
`∫(1−x)dν=0`.

For `b=(x+y)/2`, regularize at the origin. Twice integrating by parts against the
cumulative function `N(t)=ν([0,t])` gives

```text
∬ H((x+y+ε)/2) ν(dx)ν(dy)
  = −(1/2) ∫₀^∞ e^(−εs)
      (∫₀¹ e^(−sx)N(x) dx)^2 ds
  ≤ 0.
```

The kernel converges uniformly as `ε↓0`, so the unregularized quadratic form is
nonpositive.

For `c=(x+y−2xy)/2`, put `r=1−2x`, `s=1−2y`. Then `c=(1−rs)/4`, and the uniformly
convergent expansion on `|rs|≤1` is

```text
H((1−rs)/4)
  = (log 4)/4
    + (1−log 4)rs/4
    − Σ_{j≥2} (rs)^j / (4j(j−1)).
```

The constant term vanishes in the quadratic form because `ν` has total mass zero. The
linear `rs` term vanishes because

```text
∫(1−2x)dν = 0.
```

Therefore

```text
∬ H(c) ν(dx)ν(dy)
  = −Σ_{j≥2} 1/(4j(j−1))
      (∫(1−2x)^j ν(dx))^2
  ≤ 0.
```

Thus `Q(ν)≤0`, and `F` is concave on the compact convex set of probability measures
of mean `φ`.

## Extremal Supports

A minimum of a continuous concave functional on this one-moment set may be chosen at an
extreme measure, hence at a measure supported on at most two points. The remaining issue is
to exclude a minimizing support strictly inside `(0,1)`; Zargar's published argument was
stated only for `k≥3`, but at `k=2` it has a nonsingular direct form.

Suppose a minimizing measure is

```text
μ = pδᵤ+(1−p)δᵥ,
0<v<u<1,
pu+(1−p)v=φ.
```

Its first-variation potential is

```text
f(t) = 2∫g(z,t) μ(dz) − h(t).
```

If the support is minimizing, `f` lies above the line through `(v,f(v))` and
`(u,f(u))`. Hence

```text
f′(v)=f′(u),   f″(v)≥0,   f″(u)≥0,
```

while Rolle's theorem supplies a `z∈(v,u)` with `f″(z)=0`.

Direct differentiation, writing the expectation below with respect to `μ`, yields

```text
d/dt [t f″(t)]
  = −(1−2φ)/(1−t)^2
    − E[ Z/(Z+t)^2 ]
    − E[ Z(1−2Z)^2/(Z+(1−2Z)t)^2 ]
  < 0.
```

All denominators before squaring are positive for `Z,t∈(0,1)`, since
`Z+(1−2Z)t=Z(1−t)+t(1−Z)`. Thus `t f″(t)` is strictly decreasing. The zero at `z`
would force `u f″(u)<0`, a contradiction. Every extreme minimizer is consequently one of

```text
δφ,
(1−φ/x)δ₀+(φ/x)δₓ       for φ≤x≤1,
((φ−x)/(1−x))δ₁+((1−φ)/(1−x))δₓ   for 0≤x≤φ.
```

## Endpoint Optimization

The endpoint Bernoulli measure `βφ=(1−φ)δ₀+φδ₁` has

```text
F(βφ) = φ(1−2φ)L.
```

It remains to show that neither endpoint family does better.

### Support at zero

For `μ=(1−φ/x)δ₀+(φ/x)δₓ`, direct simplification gives

```text
F(μ) = φ(1−φ)B(x)/x + φ(1−2φ/x)L.
```

Therefore

```text
F(μ)−F(βφ)
  = φ/x · ((1−φ)B(x)−2φ(1−x)L).
```

The function `B(x)/(1−x)` is strictly increasing because its derivative is

```text
−log x/(1−x)^2 > 0.
```

Since `x≥φ` and concavity of binary entropy gives `B(φ)≥2φL` on
`0≤φ≤1/2`, the difference is nonnegative.

### Support at one

For

```text
μ = ((φ−x)/(1−x))δ₁+((1−φ)/(1−x))δₓ,
0≤x≤φ,
```

put `Lₓ=B((1−x)/2)`. After multiplying the desired inequality
`F(μ)≥F(βφ)` by the positive factor `(1−x)^2/(1−φ)`, it becomes

```text
A(x)+φC(x) ≥ 0,
```

where

```text
A(x) = B(x)−2xLₓ,
C(x) = 2Lₓ−(2−x)B(x)−2(1−x)^2L.
```

Two elementary calculus facts on `[0,1/2]` finish the proof:

```text
C(x) ≤ 0,
D(x) := A(x)+C(x)/2
      = xB(x)/2+(1−2x)Lₓ−(1−x)^2L ≥ 0.
```

For completeness, these inequalities have short shape certificates. On `(0,1/2)`,

```text
C‴(x) = (x^3+x^2+4x+2)/(x^2(x−1)(x+1)^2) < 0.
```

Moreover `C″(1/2)=10/3−log 16>0`, so `C″>0`; `C′` rises from `−∞` to
`log(8/3)>0`. Hence `C` decreases once and then increases. Its endpoint values are

```text
C(0)=0,
C(1/2)=log(4√3/9)<0,
```

which proves `C≤0`.

For `D`,

```text
D‴(x) = −(3x^2+7x−2)/(2x(x−1)(x+1)^2).
```

Its sign changes once, at `(√73−7)/6`. Together with

```text
D″(0+)=+∞,
D″(1/2)=log(9/4)−1<0,
D′(0+)=0,
D′(1/2)=log(3√6/8)<0,
D(0)=D(1/2)=0,
```

this shows that `D′` first rises and then falls through zero exactly once. Thus `D`
rises from zero and returns to zero, proving `D≥0`.

Finally, `C≤0` and `φ≤1/2` imply

```text
A(x)+φC(x) ≥ A(x)+C(x)/2 = D(x) ≥ 0.
```

Every extreme minimizer therefore has value at least `F(βφ)`, proving the sharp functional
inequality.

## Weighted Frankl Consequence

Zargar's semigroup lift and conditional-entropy decomposition are algebraic for every
positive integer `k,m`; their use of `k≥5` enters only through his functional theorem.
Replacing that input by the result above at `k=2,m=1` gives the following.

**Theorem.** Let `C` be a finite intersection-closed family with at least two members. Then
some coordinate `i∈⋃C` satisfies

```text
Σ_{A∈C, i∉A} 2^(−|A|)
  > (1/2) Σ_{A∈C} 2^(−|A|).
```

For the weak inequality, suppose every coordinate had strict reverse inequality. Each
coordinate entropy increment in Zargar's chain-rule decomposition would then be positive,
whereas multiplication closure of the lifted family forces the total entropy not to increase.

The conclusion is in fact strict. Suppose instead that every coordinate were present in at
least half of the weighted mass. For the base-zero probability `φ_i`, the sharp functional
bound gives a nonnegative entropy increment, and it is positive whenever `0<φ_i<1/2`.
The sum of the increments cannot be positive, so equality must hold in the total entropy
comparison. If `X,Y` are independent uniform points of the lifted multiplication-closed
family, this says

```text
H(XY)=H(X)=log |lift(C)|.
```

Thus `XY` is uniform on the lift and every one-coordinate marginal is stationary under
multiplication. In the three-element coordinate semigroup `{0,ε,1}`, with `ε²=0`, a lifted
marginal has probabilities

```text
Pr(0)=a,  Pr(ε)=a,  Pr(1)=1−2a.
```

Stationarity of the mass at `1` requires

```text
(1−2a)^2=1−2a,
```

while stationarity of the mass at `ε` requires

```text
2a(1−2a)=a.
```

The two equations have no common solution except `a=0`, which makes that base coordinate
identically one. Since a family with at least two members has a nonconstant coordinate, total
entropy equality is impossible. Hence at least one coordinate has strict weighted omission
majority.

Set complementation gives the dual union-closed form: for every nontrivial union-closed `G`,
some coordinate satisfies

```text
Σ_{A∈G, i∈A} 2^|A|
  > (1/2) Σ_{A∈G} 2^|A|.
```

## Priority Boundary

No prior source closing the binary seam was located by the 2026-08-08 cutoff. Exact searches
for `F₂,₁`, `k=2,m=1`, Zargar's title, and the two weighted conclusions returned only
Zargar's original preprint and generic Frankl literature. Semantic Scholar and OpenAlex both
reported zero indexed forward citations for the preprint. This is a bounded no-prior-source
result, not a claim about unindexed manuscripts or private communication.

The wider full-fiber architecture has a separate sharp limitation: see the
[`16/27` semigroup ceiling](frankl-semigroup-fiber-ceiling-2026-08-08.md). It rules out a
direct continuation of this method to uniform weight without ruling out use of the binary
theorem as a tilt endpoint.

## Evidence Boundary

The functional inequality and its weighted consequence are independently proved above and are
classified as audited. They do not imply Frankl's conjecture at uniform weight and do not move
the repository's universal-abundance KPI. No formalization was undertaken because no improved
universal bound is claimed; the exact formulas remain suitable for later formalization if the
tilt route makes it operationally useful.

## Source

- [Zargar 2023](../references/zargar-2023-union-closed-nonuniform-distributions.md),
  definitions of `hₖ,ₘ`, `gₖ,ₘ`, and `Fₖ,ₘ`; the entropy decomposition; Proposition 3.1;
  and the explicit `k=2,m=1` open seam in the introduction.
