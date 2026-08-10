# Frankl conjecture: the affine two-coupling wall

Date: 2026-08-10

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The independent/max-entropy affine coupling architecture has an explicit analytic obstruction at

```text
c⋆ = 0.38234553336670272114599300….
```

No affine share `α∈[0,1]`, with any nonnegative entropy slack, can certify the reduced Yu
inequality at a target `c⋆<t≤1/2`. The present Lean theorem certifies

```text
T = 38234553336670271/100000000000000000
  = 0.38234553336670271
```

with strict slack `10⁻¹⁸`. Thus the best constant accessible to this architecture is localized
to an interval of width less than `1.2×10⁻¹⁷`. This audit proves an upper obstruction; it does
not promote an exact theorem at `c⋆`.

## Defining equation

Write

```text
h(x) = −x log x − (1−x) log(1−x),    ℓ = log 2,
Φ(y) = h(y)² − ℓ(2h(y)−h(y²)).
```

Outward-rounded 160-bit Arb arithmetic certifies a sign change and positive derivative on

```text
6705452614969630276082946160/10²⁸
  < y⋆ <
6705452614969630276082946162/10²⁸,

Φ(left) < 0 < Φ(right),    Φ′ > 27/100.
```

The intermediate-value theorem and strict monotonicity therefore give exactly one zero in this
interval. Put

```text
H = h(y⋆),    Q = h(y⋆²),
s⋆ = y⋆H/Q,  c⋆ = 1−s⋆.
```

The same interval evaluation proves

```text
38234553336670272114599300/10²⁶
  < c⋆ <
38234553336670272114599301/10²⁶.
```

The executable enclosure is part of `tools/certify_frankl.py` and runs in the repository gate.
It contains no global optimizer search.

## Exact obstruction

Let `s=1−t`. On the centered diagonal-endpoint family, multiply the affine objective by its
positive scaling factor and write

```text
K(s,α,ε;y)
  = (1−α)s²h(y²)
    + α(2sy−y²)ℓ
    − (1+ε)syh(y).
```

The root equation and the definition of `s⋆` give the exact identities

```text
s⋆Q = y⋆H,
H² = ℓ(2H−Q),
s⋆H = (2s⋆−y⋆)ℓ,
s⋆²Q = s⋆y⋆H = y⋆(2s⋆−y⋆)ℓ.
```

Consequently `K(s⋆,α,0;y⋆)=0` for every `α`. Subtracting this equality at a general `s` and
using `s⋆Q=y⋆H` yields the factorization

```text
K(s,α,0;y⋆)
  = (s−s⋆)[(1−α)Qs + αy⋆(2ℓ−H)].
```

For `c⋆<t≤1/2`, one has `0<s<s⋆`. Both terms in the bracket are nonnegative, and the bracket
is strictly positive: `Q,s,y⋆>0`, while binary entropy satisfies `H≤ℓ`, hence `2ℓ−H>0`.
Therefore

```text
K(s,α,ε;y⋆) < 0
```

for every `α∈[0,1]` and `ε≥0`. The point `x⋆=1−y⋆` lies in `(1/4,1/2)` and below every such
target, so it is an admissible diagonal-endpoint law. At `t=c⋆`, every zero-slack mixture has
this equality case and every positive-slack mixture is already negative there.

## Certified lower side

Lean proves the complete finite scalar reduction and union-closed entropy bridge at

```text
t = T,
α = 356069804374481/10¹⁶,
ε = 10⁻¹⁸.
```

The independent Arb run separately certifies all three reduced objective families. Its default
run also proves

```text
11×10⁻¹⁸ < c⋆−T < 12×10⁻¹⁸.
```

If `C_aff` denotes the supremum of targets admitted by this strict affine two-coupling scheme,
the combined evidence is therefore

```text
T ≤ C_aff ≤ c⋆,    c⋆−T < 1.2×10⁻¹⁷.
```

The lower inequality is kernel-checked. The upper inequality is an independently audited
analytic factorization with a rigorous finite Arb enclosure. The exact real number `c⋆` and an
exact lower theorem at `c⋆` are not Lean declarations and are not premises of the rational
abundance theorem.

## Reproduction

Run

```text
uv run --script tools/certify_frankl.py
```

The first line localizes the affine wall. The remaining output certifies the rational target.
The strict repository transaction is `scripts/check.sh`.
