# Internal-Sandwich and Prefix-Algebra Audit

**Date:** 2026-07-25
**Targets:** reusable mortality compression; exact `M₉(2)` branch; neighboring `M₅(3)` search
**Verdict:** sandwich compiler accepted; full-algebra certificate accepted; no frontier cell
closed

This audit reconstructs the reusable mathematics from the near-killshot review. Stable records
live in `SALVAGE.md`. The general compiler is valid. The present ten-state pair is maximally
resistant to it: its word products span `M₁₀(ℚ)`.

## Internal-Word Sandwich Minimization

Let `A : Σ → M_d(K)` and use `A_{uv}=A_uA_v`. Suppose a nonempty word `ω` has nonzero product

```text
E=A_ω=UW,
```

where `U∈K^{d×r}` and `W∈K^{r×d}` both have rank `r`. Define

```text
R=span{A_w im U : w∈Σ*},
N={x∈R : WA_wx=0 for every w∈Σ*}.
```

The reachable space is invariant because

```text
A_a(A_w im U)=A_{aw} im U.
```

If `x∈N`, then for every word `v`,

```text
WA_vA_ax=WA_{va}x=0.
```

Thus `N` is invariant and every generator induces a map `B_a` on `H=R/N`.

If `A_z=0`, then `B_z=0`. Conversely, suppose `z` is nonempty and `B_z=0`. Then
`A_zR⊆N`, so `A_z im U⊆N`. The empty continuation in the definition of `N` gives `WN=0`;
hence

```text
WA_zU=0
```

and the physical repair word is zero:

```text
A_{ωzω}=EA_zE=U(WA_zU)W=0.
```

This proves mortality equivalence without a code language, parser, exterior-vector
nonvanishing condition, or restriction on the zero word downstairs beyond nonemptiness.

The matrix-valued series

```text
F(w)=WA_wU
```

has block Hankel matrix `F(uv)=WA_uA_vU`. Its natural realization on `H` is reachable by
construction and observable by the definition of `N`. Standard finite-dimensional
realization theory therefore gives

```text
dim H = rank [WA_{uv}U]_{u,v∈Σ*},
```

where the block matrix is flattened over its two boundary indices.

Over `ℚ`, compute `R` by ascending generator closure. Compute `N` as the stable term of

```text
N₀=R∩ker W,
N_{i+1}=N_i∩⋂_{a∈Σ}A_a⁻¹N_i.
```

Both chains stabilize within `d` strict dimension changes. Rational bases produce rational
quotient matrices; clearing each generator's denominator by an independent nonzero integer
preserves zero products.

If `H=0`, the mathematical equivalence says that the source family is already mortal:
`F(ε)=WU=0` gives `E²=0`. A reduction whose target convention forbids zero-dimensional
matrices must emit a fixed positive-dimensional mortal yes-instance.

The one-sided repair forms are:

```text
im A_p⊆K and A_z|K=0       ⇒ A_zA_p=0,
A_pN=0 and A_z(V)⊆N        ⇒ A_pA_z=0.
```

The first is the mechanism already formalized by `MM-C02`. The sandwich theorem composes a
reachable restriction and unobservable quotient around one internal repair word.

## The Ten-State Prefix Pair

Let `B₀,B₁` be `restrictedPrefixGenerator β body false/true` from
`PrefixMortality.lean`. Put

```text
ρ=3^β,      m=(5ρ−1)/2,      V_c^R=25+x.
```

The arithmetic source envelope gives `ρ≥27` and `body.length≥β−1≥2`. The rule-`c` lower word
has length at least five, so `V_c^R≥3⁴>25` and `x>0`. Write its lower scale as `κ=B_c^R`.

### Coordinate Reconstruction

In the ten-coordinate basis defined by `prefixCoordinate`, the generators act on basis columns
as follows:

```text
B₀e₀=me₀+e₆+(25+x)e₇+2e₈+e₉,
B₀e₁=−e₀+κe₇+3e₉,
B₀e₂=3ρe₀+3e₈,
B₀e₆=e₃,   B₀e₇=e₄,   B₀e₈=e₅,
B₀e₃=B₀e₄=B₀e₅=B₀e₉=0;
```

and

```text
B₁e₀=e₆+25e₇+((15ρ+1)/2)e₈+e₉,
B₁e₁=27e₇+3e₉,
B₁e₂=9ρe₈,
B₁e₃=e₀,   B₁e₄=e₁,   B₁e₅=e₂,
B₁e₆=e₃,   B₁e₇=0,    B₁e₈=e₅,   B₁e₉=e₄.
```

These formulas follow directly from:

- the transitions of `prefixMachine`;
- the transposed side-normal payload
  `[[1,0,0],[V,B,0],[U,0,A]]`;
- `prefixEmbed` and `prefixRetract`;
- the exact source values

```text
U_c=2,       A_c=3,
U_b=(15ρ+1)/2,   A_b=9ρ,
V_b^R=25,    B_b^R=27,
V^D=1,       B^D=3;
```

- the transposed separator row `(m,−1,3ρ)`.

A direct evaluation of the Lean definitions at `β=3`, `body=bb` reproduced every displayed
entry, including the body-dependent values `V_c^R=1508677` and `B_c^R=1594323`.

### Internal Rank-One Word

Direct multiplication gives

```text
B₀³=uvᵀ,
```

where

```text
u=(m²,0,0,1,25+x,2,m,m(25+x),2m,m)ᵀ,
vᵀ=(m,−1,3ρ,0,0,0,0,0,0,0).
```

The vector `u` is nonzero, and so is `v`; hence `B₀³` has rank one. This creates an apparent
application of the sandwich compiler to the scalar series

```text
f(w)=vᵀB_wu.
```

### Reachability Certificate

Let

```text
R=[u B₁u B₁²u … B₁⁹u].
```

Exact symbolic elimination gives

```text
det R =
(3^10/2^22) ρx(3ρ−1)^3(5ρ−3)^2(5ρ−1)(25ρ²+3)^2 P(ρ)Q(ρ,x),
```

where

```text
P(ρ)=
 158203125ρ^11−158203125ρ^10+59062500ρ^9−8812500ρ^8
 −39071250ρ^7+30457250ρ^6−9526500ρ^5+4428948ρ^4
 −664283ρ^3+40587ρ²−1032ρ+8,

Q(ρ,x)=
 46875ρ^6−56250ρ^5+28125ρ^4−18000ρ^3x−457500ρ^3
 +10800ρ²x+271125ρ²−2160ρx−54090ρ
 +512x^3+39168x²+998928x+8493267.
```

For `ρ≥27`, the negative terms of `P` below degree ten have magnitude at most
`60,000,000ρ⁸`, while its first two terms equal
`158,203,125ρ¹⁰(ρ−1)`. Ignoring the remaining positive terms proves `P(ρ)>0`.

Put `Q₀(ρ)=Q(ρ,0)`. For `ρ≥27`,

```text
Q₀(ρ)−18000ρ^6 ≥ 26000ρ^6−512000ρ^3 > 0.
```

Also

```text
Q(ρ,x) ≥ 512x³−18000ρ³x+Q₀(ρ).
```

If `0≤x≤ρ³`, the right side is at least `Q₀−18000ρ⁶>0`. If `x≥ρ³`, then

```text
512x³−18000ρ³x=x(512x²−18000ρ³)>0,
```

and `Q₀>0`. Thus `Q(ρ,x)>0` throughout the source envelope, and `det R≠0`.

### Observability Certificate

Take

```text
Pfx=(ε,1,10,11,101,110,1011,1101,10110,11010)
```

and form the matrix whose rows are `vᵀB_p` in that order. Exact symbolic elimination gives

```text
det O=3^9ρ^6(ρ−3)^3.
```

The body-dependent quantities `x` and `κ` cancel. Hence `det O≠0` for `ρ≥27`.

The audit independently reconstructed both symbolic matrices and verified:

```text
B₀³=uvᵀ,
det R=(the displayed factorization),
det O=3^9ρ^6(ρ−3)^3.
```

The executable certificate is
[`tools/audit_prefix_algebra.py`](../tools/audit_prefix_algebra.py). It uses exact SymPy
arithmetic. Its single `ty` suppression is permitted here because standalone `ty` cannot
discover a dependency installed only through the script's PEP 723 environment; Ruff, the
remaining type check, and the executable certificate remain repository gates.

The resulting Hankel section factors as `H=OR`, so the scalar series around `B₀³` has exact
Hankel rank ten.

### Full Algebra

For `0≤j≤9` and `p∈Pfx`,

```text
B₁ʲB₀³B_p=(B₁ʲu)(vᵀB_p).
```

The ten columns and ten rows are bases. Their one hundred outer products therefore form a
basis of `M₁₀(ℚ)`, and

```text
span_ℚ{B_w : w∈{0,1}*}=M₁₀(ℚ).
```

This implies irreducibility: a common invariant subspace for `B₀,B₁` would be invariant under
every matrix. Hence no nonzero proper invariant restriction or quotient exists.

More generally, take any nonzero internal word `E=UW`. Full algebra span gives

```text
span{B_w im U}=ℚ¹⁰.
```

If nonzero `ξ` were unobservable, choose a matrix `M` with `Mξ=y` and `Wy≠0`. Since `M` is a
linear combination of word products, `WB_wξ=0` for every word would imply `WMξ=0`, a
contradiction. Thus the unobservable subspace is zero. Every nonzero internal sandwich series
has exact block-Hankel rank ten.

This closes exact linear minimization of the present physical pair. It does not address a
different pair, a changed nonzero series with the same zero set, or a nonlinear compiler.

## Secondary Obstructions

### Literal Two-State Ternary Prefix Decoder

A full ternary prefix tree with five leaves has two internal states. The root has two leaf
children and one internal child; the latter has three leaf children. Give each state a
three-dimensional payload space and suppose the five decoded leaves are the four nonsingular
Neary payloads and one singular separator.

Some child leaf is nonsingular. Its decoded payload factors through the root-to-child edge, so
that edge matrix is nonsingular. The physical generator carrying it therefore makes the root
payload block available in the joint image. If its child completion is nonsingular, the same
generator supplies the child block as well. Otherwise another child completion is nonsingular;
its graph, combined with the available root block, isolates the child block. The joint image of
the three physical generators is therefore the full six-dimensional carrier.

This blocks only a common-image `6→5` restriction of a literal exact decoder.

### Additive Toggle Fusion

Normalize the paired separator to `P²=P`. The toggle obeys `T²=I`, and `LT=L` gives `PT=P`.
With

```text
Q=TP,      F=T−P,
```

one has

```text
Q²=Q,      F²=I−Q,      F³=F.
```

The rank-one idempotent `Q` makes `I−Q` rank three. Since `F³=F`, the inclusions between the
images of `F` and `F²` force `rank F=rank F²=3`. Positive powers alternate between these two
rank-three matrices. Thus this specific additive fusion has no rank-one or zero punctuation
power.

### Claims Not Promoted

The reported enumeration of `1,680` binary prefix trees was not accompanied by a preserved
checker or independently reproduced here. It is not a registry record and supports no
unbounded claim.

The proposed Carvalho/Stallings experiment is already owned by `G3-M01`; it is a research
action, not a new theorem.

## Consequences

No frontier cell changes.

- `MM-C04` supplies a new exact compression method whenever a safe family already contains a
  useful low-rank word.
- `MM-O08` closes that method, and every other exact linear subquotient, for the present
  ten-state binary pair.
- The highest-yield immediate application is to compute block-Hankel ranks around internal
  rank-two words in established six-state, three-generator families for `M₅(3)`.
- `M₉(2)` now requires a different physical pair, changed nonzero values, or a same-zero or
  nonlinear construction.
