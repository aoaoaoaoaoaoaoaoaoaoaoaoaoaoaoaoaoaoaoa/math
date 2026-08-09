# Frankl conjecture: repaired Yu reduction and rational certificate

Date: 2026-08-08

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Scope and status

This audit proves the analytic reductions needed to test Yu's coupling bound on two compact
bivariate families and records an outward-rounded Arb certificate at

```text
t = 19099/50000 = 0.38198,
α = 7/200,
ε = 1/10000000.
```

The intended conclusion is the strict entropy inequality

```text
(1−α)A(P) + αC(P) ≥ (1+ε)B(P)
```

for every finite symmetric coupling `P` of a marginal of mean at most `t`, provided
`B(P)>0`. Here, with natural logarithms,

```text
A(P) = E h(p∨q),                 p∨q = p+q−pq,
B(P) = E h(p),
C(P) = E h(median(max(p,q), 1/2, p+q)).
```

Yu's entropy theorem then gives a universal abundance bound `19099/50000`, strictly above
`(3−√5)/2`. The executable certificate passes. The result is not promoted to a
publication-facing theorem until the strict Lean formalization described in
[`FORMALIZATION.md`](../FORMALIZATION.md) also passes.

## Repairing the exact-mean reduction

Yu's proof of Proposition 1 says that `P ↦ A(P)` is concave on all symmetric couplings and
cites Alweiss–Huang–Sellke, Lemma 5. The cited lemma proves concavity only on a slice with
fixed marginal mean. Global concavity is false. The reduction is repaired before that lemma
is used.

Let a symmetric coupling `P` have marginal mean `s<t`, and put

```text
γ = (t−s)/(1−s),
P′ = (1−γ)P + γδ_(1,1).
```

The marginal of `P′` has mean exactly `t`. Since every entropy integrand vanishes when one
input is `1`,

```text
A(P′) = (1−γ)²A(P),
B(P′) = (1−γ)B(P),
C(P′) = (1−γ)C(P).
```

Consequently,

```text
((1−α)A(P′)+αC(P′))/B(P′)
  = (1−α)(1−γ)A(P)/B(P) + αC(P)/B(P)
  ≤ ((1−α)A(P)+αC(P))/B(P).
```

It is therefore enough to minimize on the exact-mean slice, where the cited concavity theorem
does apply.

For a finite support, every symmetric coupling is a convex combination of orbit laws

```text
Q_(x,y) = (δ_(x,y)+δ_(y,x))/2.
```

Intersecting that simplex with the one exact-mean equation gives extreme points supported on
at most two orbits, whose orbit means straddle `t`; a one-orbit extreme has mean `t`. Since
`A` is concave on the slice and `C−B` is linear, a negative gap would occur at one such
extreme point.

## Removing support above one half

For `y∈(1/2,1)`, write `z=1−y` and replace `y` by the mean-preserving law

```text
κ_y = 2z δ_(1/2) + (1−2z)δ_1.
```

Apply this kernel independently to both coordinates of the coupling. Symmetry and marginal
mean are preserved. For the dependent cost

```text
c(x,r)=h(median(max(x,r),1/2,x+r)),
```

one has `E c(κ_y,r)≤c(y,r)` pointwise:

- if `r≤1/2`, this is `2z log 2≤h(z)`;
- if `1/2<r≤y`, monotonicity of `h` on `[1/2,1]` reduces to the preceding inequality;
- if `r≥y`, it is the factor bound `2z≤1`.

Thus `C` does not increase.

It remains to compare the independent and marginal terms without Cambie's infinitesimal
`O(η)` remainder. Put

```text
w = (1+ε)/(1−α),
g_y(x) = 2z h((1−x)/2) − h(z(1−x)).
```

Direct differentiation shows that `g_y` is increasing and concave on `[0,1]`. There is a
clean finite comparison, so no infinitesimal path or integration remainder is needed. Let `μ`
be the old marginal, let `μ′=μ+λ(κ_y−δ_y)` be the replaced marginal, and write
`A(μ)=E_(μ×μ)h(p∨q)`. Bilinear polarization gives the exact identity

```text
A(μ′)−A(μ) = λ(E_μ g_y + E_μ′ g_y).
```

Both marginals have the same mean, at most `t`. Jensen's inequality and monotonicity therefore
give `E_μ g_y,E_μ′ g_y≤g_y(t)`, whereas

```text
B(μ′)−B(μ)=λg_y(0).
```

Thus `w(B(μ′)−B(μ))−(A(μ′)−A(μ))` is at least
`λ(wg_y(0)−2g_y(t))`.

Set `r=1−t`. The opposite quantity is

```text
F(z) = 2g_y(t)−wg_y(0)
     = z(4h(r/2)−2w log 2) + wh(z)−2h(rz).
```

It vanishes at `z=0,1/2`, and

```text
zF″(z) = −w/(1−z) + 2r/(1−rz).
```

The numerator `2r(1−z)−w(1−rz)` is linear, positive at zero and negative at one half.
Moreover,

```text
F′(1/2) = −4 log((1+t)/2) − 2w log 2 > 0.
```

Hence `F′` first increases and then decreases, crosses zero once, and remains positive at the
right endpoint. Since both endpoint values of `F` vanish, `F(z)<0` for `0<z<1/2`.
The polarized finite comparison proves that the full gap does not increase. Every relevant
extreme may therefore be assumed to use only `[0,1/2]∪{1}`.

## Contracting the surviving low orbits

For `0≤a−d≤a+d≤1/2`, let

```text
ν_(a,d) = (δ_(a−d)+δ_(a+d))/2,
Δ(a,d) = h(a)−E_ν h ≥ 0.
```

The dependent cost of the orbit `Q_(a−d,a+d)` is

```text
h(min(2a,1/2)),
```

so it is unchanged when the orbit is contracted to `δ_(a,a)`.

### Curvature comparison

For fixed `q`, put `f_q(x)=h(x∨q)`. On the open unit interval,

```text
|f_q″(x)| / |h″(x)| = x(1−q)/(x+q−xq).
```

For `x,q≤1/2`, this gives both

```text
x(1−q)/(x+q−xq) ≤ (1−q)/(1+q) ≤ 1−4q/3.
```

Thus concavity of `λh−f_q` implies the Jensen-deficit estimates

```text
f_q(a)−E_ν f_q ≤ ((1−q)/(1+q))Δ(a,d)
               ≤ (1−4q/3)Δ(a,d).
```

The weaker bound with coefficient `1−q` remains valid for `q∈[0,1]`.

### Self-pair estimate

The additional estimate

```text
h(a∨a)−E_(ν×ν) h(p∨q) ≤ Δ(a,d)
```

holds throughout the low square. In complement coordinates

```text
x=1−a+d,   y=1−a−d,   1/2≤y≤x≤1,
R(u)=u h′(u²)−h′(u),
K(x,y)=R(x)−R(y)−(x−y)h′(xy),
```

the derivative of `E_(ν×ν)h(p∨q)−E_νh(p)` with respect to `d` is `K(x,y)/2`.
Now `K(y,y)=0` and

```text
K(1,y)=log 2−y log(1+1/y) ≥ 0.
```

For fixed `y`, `K` is concave in `x`. After clearing the positive denominator, the assertion
`K_xx≤0` is the polynomial inequality `−P(x,y)≥0`, where

```text
P = 2x⁴y²−x⁴−x³y²−x³y−x³−3x²y²+5x²y+x²
    −2xy²+3xy−2x+y−1.
```

With barycentric coordinates

```text
u=2(1−x),   v=2(x−y),   z=2y−1,   u+v+z=1,
```

the degree-six Bernstein coefficients of `−P` are all nonnegative:

```text
(0,0):0  (0,1):0  (0,2):1/15  (0,3):1/5  (0,4):2/5  (0,5):2/3  (0,6):1
(1,0):0  (1,1):1/30  (1,2):61/480  (1,3):9/32  (1,4):119/240  (1,5):37/48
(2,0):0  (2,1):1/12  (2,2):13/60  (2,3):2/5  (2,4):19/30
(3,0):3/40  (3,1):191/960  (3,2):139/384  (3,3):361/640
(4,0):13/60  (4,1):35/96  (4,2):13/24
(5,0):25/64  (5,1):35/64
(6,0):9/16.
```

The indices shown are the powers of `u,v`; the remaining Bernstein index is
`6−i−j`. Concavity between the two nonnegative endpoint values proves `K≥0` and hence the
self-pair estimate.

Sequential curvature comparison also gives the sharper mean-dependent bound

```text
h(a∨a)−E_(ν×ν)h(p∨q) ≤ 2(1−4a/3)Δ(a,d).
```

### Two-orbit contraction

Suppose first that the two orbit means satisfy `a≤t≤b≤1/2`, with weights

```text
W=(b−t)/(b−a),   β=(t−a)/(b−a).
```

Contract the lower orbit first. Its independent-entropy increase is at most

```text
WΔ(a,d)[W+2β(1−4b/3)] ≤ WΔ(a,d),
```

because `b≥t>3/8`. After that contraction, contract the upper orbit. Its independent-entropy
increase divided by its marginal-entropy increase is at most

```text
2β(1−4b/3) + 2W(1−a)/(1+a)
  ≤ 2−8t/3
  = 18401/18750
  < 1.
```

The difference between the left side and `2−8t/3` factors as

```text
4a(2a−1)(t−b) / (3(1+a)(a−b)) ≤ 0.
```

If the upper orbit is `Q_(q,1)`, its mean is at least one half. Contracting the low orbit has
independent-entropy increase at most

```text
WΔ(a,d)[W+β(1−q)] ≤ WΔ(a,d).
```

In every step `C` is fixed, while `A` rises by no more than `B`. Since the coefficient of `A`
is `1−α` and that of `B` is `1+ε`, contraction cannot increase the target gap.

The only remaining extreme families are therefore diagonal–diagonal and
diagonal–endpoint.

## The two exact objectives

For the diagonal–endpoint family

```text
P = (1−β)δ_(a,a) + βQ_(q,1),
β = 2(t−a)/(1+q−2a),
0≤a≤t,  0≤q≤1,
```

the three terms are

```text
A = (1−β)²h(2a−a²)
    + β(1−β)h(a+q−aq)
    + (β²/4)h(2q−q²),
B = (1−β)h(a) + (β/2)h(q),
C = (1−β)h(min(2a,1/2)).
```

For the diagonal–diagonal family

```text
P = (1−β)δ_(a,a) + βδ_(b,b),
0≤a≤t≤b≤1/2,
```

the corresponding formulas are

```text
A = (1−β)²h(2a−a²)
    + 2β(1−β)h(a+b−ab)
    + β²h(2b−b²),
B = (1−β)h(a)+βh(b),
C = (1−β)h(min(2a,1/2))+βh(min(2b,1/2)).
```

The exact-mean constraint is parameterized without a singular `b−a` denominator. For
`0≤β≤2t`, take

```text
b=t+v(1/2−t),
a=t−βv(1/2−t)/(1−β).
```

For `2t≤β≤1`, take

```text
a=t(1−v),
b=t+(1−β)vt/β.
```

In both cases `0≤v≤1`.

## Entropy-zero corners

The diagonal–endpoint gap vanishes at `(a,q)=(0,0)` and `(0,1)`, where `B=0`.
Interval derivatives are singular there, so two squares of side `δ=1/1000` are proved
analytically.

For `a,q≤δ`, the estimates

```text
h(2x−x²) ≥ (9/5)h(x),
h(2x) ≥ (9/5)h(x),
h(a∨q) ≥ h(a)+h(q)−(a∨q)log 3
```

reduce the gap to positive multiples of `h(a),h(q)` minus
`(1−α)β(1−β)(a+q)log 3`. The coefficient bounds, together with

```text
h(x)≥x log(1/x),
log 1000>69/10,
log 3<11/10,
```

leave rational margins `>0.1499` and `>0.1180` after division by `a+q`.

For `a≤δ` and `1−q≤δ`, write `r=1−q`. Concavity gives

```text
h(r(1−a)) ≥ (1−a)h(r).
```

Here `β<2/5` and `1−β>3/5`. Dropping the nonnegative `q∨q` term leaves positive
coefficients; the two rational inner margins exceed `0.105` and `0.078`.

## Analytic collapse of the diagonal family

The diagonal–diagonal region admits a stronger argument than interval subdivision. Let a
binary law on `[0,1/2]` have masses `ℓ,u`, support `a,b`, and exact mean `t`, and put

```text
Δ = h(t)−ℓh(a)−uh(b) ≥ 0.
```

Applying the sharp join-curvature bound to the center row and the affine bound to the two
outer rows gives

```text
h(t∨t)−E h(X∨Y)
  ≤ ((1−t)/(1+t) + 1−4t/3)Δ.
```

The dependent term has a separate two-to-one comparison. Define

```text
g(x)=2h(x)−h(min(2x,1/2)).
```

On `[0,1/4]`, `g(x)=2h(x)−h(2x)` and

```text
g″(x)=2/((1−2x)(1−x)) ≥ 0.
```

Thus `g` lies below the chord through `0` and `1/4`. Both chord endpoints lie below the
entropy tangent at `t`: the `1/4` endpoint is ordinary concavity of `h`, while the zero
endpoint reduces to

```text
−log(2(1−t)²) ≥ 0.
```

Above `1/4`, the same supporting-line inequality is twice the entropy tangent inequality.
Averaging it at mean `t` yields

```text
log 2−E h(min(2X,1/2)) ≤ 2Δ.
```

At the certified parameters the combined loss coefficient is

```text
(193/200)((1−t)/(1+t)+1−4t/3)+(7/200)·2
  = 56146740823/57582500000,
```

which is below `10000001/10000000` by
`5743059741/230330000000`. Every two-diagonal objective is consequently bounded below by
the point-mass objective. The exact dual evaluator at that rational point gives the
kernel-replayed lower bound

```text
1102953606749615/1152921504606846976 > 0.
```

`Frankl/DiagonalObjective.lean` formalizes the supporting line, the convex low branch, both
deficit estimates, their exact coefficient comparison, the point enclosure, and the resulting
nonnegativity of the full lower and upper diagonal coordinate rectangles.

## Endpoint-core contraction

Write `β` for the endpoint-orbit mass and `m=1−β/2` for the total mass of the two
nondeterministic coordinate values. Conditioning that subprobability law gives weights

```text
ℓ=(1−β)/m,     u=(β/2)/m
```

on `a,q`, with conditional mean

```text
r = ℓa+uq = (a(1−2t)+tq)/(1+q−a−t).
```

The independent and marginal entropies of the endpoint objective are respectively `m²` and
`m` times those of this conditional binary law. If `a≥1/4`, `q≤1/2`, and `r≥13/50`, the
dependent term is unchanged by contracting `a,q` to `r`: both its original and centered
diagonal costs are `log 2`. It therefore suffices that

```text
(1−α)m((1−r)/(1+r)+1−4r/3) ≤ 1+ε.
```

The exact-mean relation gives `m=(1−t)/(1−r)`. After clearing the positive factors
`1−r` and `1+r`, the left side is monotone decreasing on the core interval. At its boundary
`r=13/50`, it is

```text
5826723461/5827500000,
```

below `10000001/10000000` by `3108487/23310000000`. Consequently

```text
J(r,r) ≤ J(a,q)
```

throughout the endpoint core. `Frankl/EndpointObjective.lean` formalizes the generic scaled
Jensen-deficit contraction, the exact coefficient inequality, all conditional-weight and
mean identities, and its specialization to the certificate coordinates. Positivity of the
centered curve and certification of the complementary endpoint wedge remain separate
obligations.

## Outward-rounded certificate

[`tools/certify_frankl_38198.py`](../tools/certify_frankl_38198.py) uses
`python-flint 0.9.0` at 160-bit Arb precision. Rational boxes are enclosed exactly. Each box
is discharged either by natural interval evaluation, by a first-order mean-value enclosure
whose derivative bounds cover the entire box, or by a derivative sign that moves the minimum
to an exact face. Entropy intervals touching zero or one are enclosed by endpoint monotonicity.
No floating-point value participates in a positivity decision; floats order the work queue only.

The deterministic run reports:

```text
scalar lemmas: certified
diagonal-endpoint: 14600 assessed boxes; 7319 certified leaves
diagonal-endpoint: sha256 e44c8f3f4cceefdbe394642a5416900592cf0eac30b1d1a6961a28bf4ab8fd1e
diagonal-diagonal-lower: 2914 assessed boxes; 1465 certified leaves
diagonal-diagonal-lower: sha256 82f7326f5cd2fe87f58157c1a00a8f732b2b490bae2b619b00dd8e80dc7f92da
diagonal-diagonal-upper: 1626 assessed boxes; 819 certified leaves
diagonal-diagonal-upper: sha256 f870f4f48e71c34e49bb9cf4e2b7b365d3280c7b4b2a61ff3e4cc8575e8b245c
Frankl entropy certificate at 19099/50000: PASS
```

## Kernel-checked certificate architecture

The formal development now owns the certificate mathematics rather than trusting Arb. It
defines the three exact rational coordinate rectangles and objective expressions, proves that
their semantics are the reduced objectives above, and checks every domain obligation. Its
rational ball arithmetic has outward dyadic rounding. Logarithms use four odd terms of

```text
log((1+z)/(1−z)) = 2(z+z³/3+z⁵/5+z⁷/7+⋯)
```

with proved error `2|z|⁹/(1−|z|)`, after power-of-two scaling and a proved rational
enclosure of `log 2`. Entropy and coordinate-derivative enclosures are derived from these
primitives. A first-order mean-value leaf, rational subdivision checker, and adaptive seeded
generator are proved sound; direct recursive adjudication is proved equal to checking its
generated tree. The two singular endpoint squares are discharged by the analytic inequalities
in the preceding section, now formalized without numerical oracles.

At parameters `(order,fuel,bits,depth)=(12,64,32,32)`, exact executable reduction of the Lean
definitions returns `some ()` for the endpoint, lower-diagonal, and upper-diagonal rectangles.
The joint replay took `9:03.89` wallclock, `530.79` user seconds, and `1,813,464 KiB` peak RSS
under Lean 4.12.0. The subsequent analytic argument above has replaced both diagonal verdicts
with kernel theorems. The endpoint verdict remains stronger implementation evidence than the
independent Arb run, but is not yet a kernel theorem. Naive reduction of its rational expression
tree inside the kernel has prohibitive time and memory behavior even on small seeded cells. The
remaining certificate obligation is therefore to produce a compact endpoint proof trace,
strengthen its analytic or monotonicity leaves enough to collapse the tree, or replace general
rational reduction with a proved fixed-point checker.

## Evidence boundary

The analytic reduction above corrects two distinct weaknesses in the source chain: Yu's use
of fixed-mean concavity as though it were global, and Cambie's infinitesimal support movement.
The Arb result is an independently replayable rigorous numerical certificate, but the project
standard additionally requires kernel-checked formalization before the improved universal
constant is advertised as established. Until that gate closes, this audit is evidence for a
candidate theorem rather than a publication claim.

Primary sources:

- [Yu, *Dimension-Free Bounds for the Union-Closed Sets Conjecture*](../references/yu-2023-dimension-free-bounds-union-closed-journal.md)
- [Alweiss–Huang–Sellke, *Improved Lower Bound for Frankl's Union-Closed Sets Conjecture*](../references/alweiss-huang-sellke-2024-improved-lower-bound-frankl-journal.md)
- [Cambie, *Better Bounds for the Union-Closed Sets Conjecture Using the Entropy Approach*](../references/cambie-2022-better-bounds-union-closed.md)
