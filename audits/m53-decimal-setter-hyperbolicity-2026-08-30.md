# Decimal Setter Hyperbolicity Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the setter survives radix ten with digits `0 ↦ 7`, `1 ↦ 5`, and every
square-run transfer is strictly hyperbolic; positive-ray certificates still fail at arbitrary
depth

Nothing below proves projective avoidance or `M₅(3)`.

## Radix-Parametric Setter

Let a binary word be evaluated in radix `B` with distinct nonzero digits

```text
0 ↦ d₀,       1 ↦ d₁,       0<d₁<d₀<B.
```

The code is injective and concatenative. Put

```text
μ=[10^β]_B,       t=B^(β+1),       r=t/μ.
```

For the distinguished upper letter `c`, one has `U_c=d₁` and `A_c=B`. Assume

```text
e=B−1−rd₁ ≠ 0.
```

The setter construction is unchanged after replacing its side basis by

```text
f=(1,0,r)ᵀ,       p=(0,−1,0)ᵀ,       q=(0,0,re)ᵀ.
```

Indeed, the side-normal rule and erasure matrices satisfy

```text
R_cf=D_cf=(1+rd₁)f+q.                     (1)
```

The basis determinant is `−re`. The source boundary is still exact because

```text
[f p q](μ,1,0)ᵀ=(μ,−1,t)ᵀ.
```

Write

```text
α=1+rd₁,       λ=α/μ.
```

With the same five-dimensional delimiter and boundary vectors as in the ternary setter, direct
multiplication again gives

```text
rank S=3,       rank S²=2,       rank S³=1,
Sⁿ=S³  for n≥3,
S²A_cS³=λC̃L̃.                              (2)
```

Thus the regular decoder, internal rank-one separator, and halting-to-mortality implication do
not depend on radix three. Clearing the nonzero rational denominators of each generator produces
integer matrices without changing which products vanish.

## Decimal Specialization

Take

```text
B=10,       d₀=7,       d₁=5,       ρ=10^β.
```

The Neary compiler emits `β=10·period`, so in particular `β≥10`. Exact simplification gives

```text
μ=(52ρ−7)/9,
r=90ρ/(52ρ−7),
e=9(2ρ−7)/(52ρ−7)>0,
L=α/e=(502ρ−7)/(9(2ρ−7)),
C=L/μ=(502ρ−7)/((2ρ−7)(52ρ−7)).            (3)
```

For a nonempty role block `z`, let `m` and `n` be the upper and lower spelling lengths, let
`A=10^m`, and put

```text
P=μ+10ρU,       V=[lower(z)]₁₀.
```

In the scaled projective coordinate `y=μx`, the transfer is

```text
Ψ_z(y)=−L(1−μA/(P−Vy)).                     (4)
```

Conjugate by

```text
t=L/(y+L),       u=P/(μA),       v=LV/(μA).
```

Then every transfer is the negative J-fraction step

```text
F_z(t)=u+v−v/t,       pole(F_z)=v/(u+v),
disc(F_z)=(u+v)²−4v.                         (5)
```

Both `u` and `v` are positive.

## Length-Shell Theorem

The sign of `u−1` is fixed by the first upper role. A `b` role begins with the marker
`10^β` and then has another nonzero digit, so `u>1`. A `c` role has second digit `5`, below the
marker digit `7`, so `u<1`. In the latter case, its leading digit alone gives

```text
u≥u₀:=45ρ/(52ρ−7).                           (6)
```

Every nonempty decimal `5/7` word satisfies

```text
1/2 ≤ V/10^n < 7/9.                         (7)
```

Set `δ=n−m`. Equations (3) and (7) split all lower scales at one integer wall:

```text
δ≤β−1  ⇒  v≤v₋:=7ρC/90,
δ≥β    ⇒  v≥v₊:=ρC/2.                       (8)
```

For `u>1`, strict hyperbolicity follows from `u+v>1+v≥2√v`. For a `c`-leading block,
the discriminant is increasing in `u`, so it suffices to use `u₀`. As a function of `v`,
`(u₀+v)²−4v` decreases before `2−u₀` and increases afterwards. Direct subtraction gives

```text
v₋−(2−u₀)=
−(7106ρ²−39641ρ+8820)/(90(2ρ−7)(52ρ−7))<0,

v₊−(2−u₀)=
7(2ρ+7)(19ρ−4)/(2(2ρ−7)(52ρ−7))>0.         (9)
```

The two endpoint discriminants are

```text
(u₀+v₋)²−4v₋ =
ρ(3320836ρ³−179632292ρ²+737848321ρ+864360)
  / (8100(2ρ−7)²(52ρ−7)²),

(u₀+v₊)²−4v₊ =
7ρ(6780ρ³+93572ρ²+26831ρ+392)
  / (4(2ρ−7)²(52ρ−7)²).                    (10)
```

The second numerator is positive. The first is positive for `ρ≥55`, since its first two terms
already have positive sum there and its remaining terms are positive. Equations (8)–(10) prove:

> **Decimal hyperbolicity theorem.** For `β≥2`, every nonempty square-run block in the
> decimal `0 ↦ 7`, `1 ↦ 5` setter induces a strictly hyperbolic orientation-preserving
> projective transfer. No parabolic block exists.

This removes the balanced elliptic corridor that survives in radix three. It does not separate
an arbitrary rational orbit from the poles.

## Finite-Ray Obstruction

Strict hyperbolicity does not yield a finite last-block ray certificate. Consider any proposed
finite labelled invariant whose domain at label `i` is a positive ray `[r_i,∞]`, and suppose
every square-run block may follow every label, as the fracture grammar permits.

Blocks containing increasingly many `c` rules have `v→∞`, hence poles `v/(u+v)→1` from below.
Pole avoidance therefore forces

```text
r_i≥1                                                   (11)
```

for every source label.

The single `c` erasure has

```text
u_c=(502ρ−7)/(10(52ρ−7)),
v_c=7C/10,
a_c=u_c+v_c<1.                              (12)
```

The last inequality is equivalent to

```text
36ρ²−3766ρ+490>0,
```

and therefore holds throughout the emitted range. For every `t≥1`,

```text
F_Dc(t)=a_c−v_c/t<a_c<1.                    (13)
```

Equations (11) and (13) are contradictory: a `D_c` transition cannot land in any labelled
positive ray. Splitting labels by first role, last role, or low/high length shell does not help,
because the next square-run block is arbitrary. A viable invariant must be two-sided, carry an
unbounded rescaling, or use arithmetic information beyond a finite family of positive rays.

## Boundary

Exact bounded orbits for the small body `bcbbbbbbc` support the decimal candidate but do not
promote it: all role blocks of length at most two avoid every pole through four transfers
(`208000` distinct states at depth four). The negaternary variant and unlabelled convex chambers
were also tested and rejected; neither supplies a uniform invariant for arbitrary block length.

The live target is an arithmetic J-fraction invariant combining the decimal length split with
suffix or `2`/`5`-adic carry. Hyperbolicity is now free; arbitrary-depth pole avoidance is not.
