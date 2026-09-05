# Eight-state asymmetric return audit

**Date:** 5 September 2026. **Baseline:** `30687d1621c763dd81dbabebb5d1d393288b06e2`.

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva.

**Status:** independently reconstructed pen-and-paper reduction; Lean-checked compiler prefix,
fixed chart, complete return sequence, and source-parameter regularity. The complete M₈(2)
endpoint is **not yet formalized**. The public
table remains unchanged until that endpoint and its verification gate exist.

## Verdict

The proposed asymmetric construction passes this audit. It retains the paired data roles,
changes the separator row, and rescales the toggle. Its separator preserves existence of a
scalar zero, not the pointwise zero language. Every actual universal-compiler body has the
prefix needed to exclude its unwanted phase.

The complete mathematical chain is present: universal source, unrestricted scalar converse,
eight-dimensional realization, unrestricted physical products, effective integerization.
No new source-hardness conjecture or bounded-word assumption is needed. The outstanding work
is to reconstruct that chain in Lean, not to find another mathematical mechanism.

The local audit did not use the discovery report's attached programs. The retained checker
reconstructs the roles, verifies the rational identities, and emits a different, fixed-basis
chart. This removes the discovery construction's rank-testing basis selection entirely.

## Source and coordinates

Let β ≥ 3 and let the body be `bcb` followed by an arbitrary tag word. Write

```text
H(b)=10^β1, H(c)=1, W=H(body), L=|W|,
ρ=3^β, K=3^(L+3), V=σ(1W10),
```

where σ encodes binary symbols 0 and 1 as ternary digits 1 and 2. The existing paired roles are

```text
B = [1 25 (15ρ+1)/2 1]      D = [1 V 2 1]      T = [1 0 0 0]
    [0  0     0     0]          [0 0 0 0]          [0 0 0 1]
    [0  0    9ρ     0]          [0 0 3 0]          [0 0 1 0]
    [0 27     0     3]          [0 K 0 3]          [0 1 0 0]

u = ((5ρ−1)/2, 0, 3ρ, −1)ᵀ.
```

These agree with `ChangedSeparatorRealization.chainDataB`, `chainDataC`, and
`chainTailColumn`. The column is the existing boundary after absorbing a trailing toggle.
`PairedBinaryPrefixTax.pairedTrailingToggle_hasNonemptyZero_iff` transports the existential
zero predicate back to the original paired source.

Set

```text
θ=σ(W)/(3^L−1), q=−1−θ=(K−3V+48)/(K−27),
a=16+9q, r=(1,a,q,q), F_c(X)=σ(X)+c·3^|X|.
```

Both binary symbols occur in W, so 1/2 < θ < 1 and −2 < q < −3/2. Rotating its initial `10`
to the end gives a word whose periodic fraction is η=9θ−7. It also contains both symbols;
hence 1/2 < η < 1 and a=−η lies strictly between −1 and −1/2.

The compiler fact is now a separate checked declaration:

```lean
MatrixMortality.Undecidability.NearyCompiler.body_take_three
```

It states that every emitted body has `take 3 = [.b, .c, .b]`. Its proof reads the first
column of Table 2 through `weave_get_track`; phases 0, 1, 2 are constant b, c, b, and none
is the final phase. The woven appendant has length greater than three, so `dropLast` preserves
these entries. This is not an inference from a benchmark or from `body_head_b` alone.

## Unrestricted scalar converse

Induction through the paired decoder gives, for every raw control product P, one of

```text
Pu = (σ(X)−σ(Y), 0,       3^|X|, −3^|Y|)ᵀ,
Pu = (σ(X)−σ(Y), −3^|Y|, 3^|X|, 0)ᵀ.
```

Here X is the decoded upper word followed by the marker, and the lower word belongs to
`{0,110,1W10}*`. No legality condition is imposed on the controls. In the first phase, rPu is
`F_q(X)−F_q(Y)`; the existing tilted-code injectivity theorem makes its zero set exactly X=Y.

Suppose the second phase vanishes: `F_q(X)=F_a(Y)`. Clear the common denominator `3^L−1`,
which is coprime to 3, and reduce modulo `3^min(|X|,|Y|)`. Uniqueness of the last ternary
digits makes the shorter word a suffix of the longer.

Equal lengths force X=Y and q=a, impossible. If X=pY with nonempty p, cancellation gives
`F_q(p)=a`, whereas

```text
F_q(p) ≤ −1−θ·3^|p| < −5/2 < a.
```

Thus Y=pX with k=|p|>0. Cancellation and the definitions give

```text
q=σ(p)+a·3^k,
θ=(σ(10p)+1)/(3^(k+2)−1).                         (1)
```

There is a finite proof of the periodic-word step. W ends in binary 1, so σ(W) is 2 modulo
3. Clearing (1) and reducing modulo 3 forces `σ(10p)+1` to be 2 modulo 3. Therefore p ends
in binary 0. Replace that last symbol by 1, obtaining p⁺, and put Z=10p⁺. Then
`σ(Z)=σ(10p)+1`. Repeating both blocks to length L(k+2), equation (1) gives equal ternary
codes, hence

```text
W^(k+2)=Z^L.                                    (2)
```

This avoids an appeal to uniqueness of infinite radix expansions, including its endpoint
ambiguity. The common word in (2) is long enough for every comparison below.

The formalization has a shorter finite replacement: cross-multiplying the periodic fractions
is exactly equality of the codes of WZ and ZW. `periodicTernaryCode_eq_iff_commute` proves this
equivalence for nonempty blocks. The five cases can therefore compare these concatenations
directly instead of constructing the repetitions in (2). This arithmetic-to-word step is
checked; the complete five-case exclusion is not yet a Lean theorem.

The suffix after the initial `10` in W starts `0^(β−1)1110^β1`. The word p⁺ is a prefix of
that periodic suffix and ends in 1. There are five exhaustive cases.

1. If k ≤ β−1, its final symbol is 0, a contradiction.
2. If k=β, Z=H(b). After its first period the source continues `11`, but Z continues `10`.
3. If k=β+1, p=`0^(β−1)10`. It cannot prefix a lower word: the first nonzero lower tile
   starts `110`, not `10`.
4. If k=β+2, Z=H(bcc). The next symbol of Z's repetition is 1; the source's next symbol
   is the first zero inside its third letter b.
5. If k ≥ β+3, p begins `0^(β−1)111`. This again conflicts with the lower word's first
   nonzero tile, which starts `110`.

Consequently the second phase never vanishes. We have proved

```text
rPu=0  iff  Pu is in the erase phase and X=Y.       (3)
```

A leading toggle switches phase and preserves the old first-coordinate coefficient. It follows
that `∃P, rPu=0` iff `∃P, e₀ᵀPu=0`. The empty product has neither zero coefficient: its
upper word is the nonempty marker and its lower word is empty.

## Eight-state realization

Define

```text
t=2q+1, h=6/[t(3ρ−1)], ξ=3ρ+1+ρh,
Δ=K((t−2)ρ−t)+26t+72,
γ=K[t(27ρ³−1)+18ρ²+6ρ]/Δ, R=hur.
```

The required returns are γT, B, D at times 0, 1, 2 and `ξ^(2−n)R` at every n≥3.
On the source domain, −3<t<−2, ρ≥27, and K>27. Thus h<0 and
`|ρh|<3ρ/(3ρ−1)<2`, so ξ>0. Also

```text
Δ < K(2−4ρ)+20 < 0,
t(27ρ³−1)+18ρ²+6ρ < −54ρ³+18ρ²+6ρ+2 < 0.
```

Hence γ>0; every division below has a nonzero denominator.

Subtract the extrapolated geometric contribution:

```text
F₀=γT−ξ²R, F₁=B−ξR, F₂=D−R.
κ=(K−3V,3,0,−K)ᵀ, z=((3ρ−1)/6,0,ρ,−1/3)ᵀ,
ℓ=(1,0,(q−2)/3,(q−1)/3).
```

The independently checked rational identities give

```text
Dκ=0, Dz=u, ℓD=r, h·rz=1,
ℓBκ=0, ℓBz=ξ·rz.
```

Thus F₂ has rank two, kernel span{κ,z}, and image `ker e₁ᵀ ∩ ker ℓ`; F₁ maps its kernel
into its image. The additional reader

```text
w=(1−ξ, 0, ((15ρ+1)/2−2+(3ρ−ξ)(q−2))/3, (1−ξ)(q−1)/3)
```

satisfies `wu=0`, `wF₂=ℓF₁`. Both rows of the remaining Schur complement annihilate
`ω=κ−3Kz`; the row `e₁ᵀF₀` has values `(−γK,−γ/3)` on κ,z and is nonzero. The block
Hankel matrix with rows `(F₀,F₁,F₂)`, `(F₁,F₂,0)`, `(F₂,0,0)` therefore has rank seven.
This explains the `3+3+1` transient, but the emitter need not compute a Hankel basis.

### Fixed chart

Here is a fixed rational factorization reconstructed during the audit. It replaces the
discovery report's choice of seven independent Hankel columns. Let E have columns e₀,e₂ and

```text
G = [0 0 −q/3 (3ρ−t)/6],
    [0 0  1/3     ρ    ]

Q₂ = [1  a+K(3ρ−t)/6  0  (3ρ−1)/2],
     [0       ρK      1      3ρ    ]

Lᵢ=FᵢE,
Q₁=G(F₁−L₁Q₂), Z₀=F₀−L₀Q₂−L₁Q₁,
j=−3Z₀z/γ, f=(0,0,0,γ), Q₀=G(Z₀−jf).
```

Direct rational identities prove

```text
GL₂=I₂,
F₂=L₂Q₂,
F₁=L₁Q₂+L₂Q₁,
F₀=L₀Q₂+L₁Q₁+L₂Q₀+jf.                           (4)
```

On coordinates `(x₀,x₁,x₂,s,g)` of sizes `2,2,2,1,1`, set

```text
A(x₀,x₁,x₂,s,g)=(0,x₀,x₁,0,ξ⁻¹g),
Uz=(Q₂z,Q₁z,Q₀z,fz,ξ²h·rz),
O(x₀,x₁,x₂,s,g)=L₀x₀+L₁x₁+L₂x₂+js+ug,
C=UO.
```

Equation (4) proves the first three returns. The nilpotent part dies at time three, leaving
`OA^nU=ξ^(2−n)R` for every n≥3. The geometric coordinate also proves Aⁿ≠0 for every n.
Only rational arithmetic is used. There is no rank test, case-selected basis, or additional
denominator arising from a pivot choice.

## Physical words and effectivity

Every return is a nonzero scalar multiple of one of γT,B,D,R, and times 0,1,2,3 supply all
four roles. The existing singular-return theorem therefore gives

```text
Mortal{A,C} iff Mortal{γT,B,D,R}.
```

This includes arbitrary exterior powers of A. A cut-free word is nonzero by the geometric
coordinate; a cut-containing zero can be sandwiched by O and U to obtain a zero return word.
Conversely, surrounding a zero return product by U and O supplies an actual cut-containing
physical word.

Rescaling T by γ changes no scalar zero. Pure control products preserve the nonzero e₀-line.
In a word containing R, the outer column is nonzero because its upper-scale coordinate remains
nonzero, and the outer row is nonzero because its value on e₀ remains nonzero. Thus a product
containing separators vanishes exactly when an interior coefficient rPu vanishes. Empty
interiors contribute ru≠0. With (3), this proves mortality iff the inherited source halts.

The fixed chart consists of powers, word codes, and rational arithmetic on fixed-size arrays.
These operations are primitive recursive in the repository's coding. Independent nonzero
denominator clearing for A and C preserves and reflects zero products. Composing with the
existing primitive-recursive universal source gives the proposed standard M₈(2) endpoint.
This paragraph is an effective mathematical construction, **not a claim that its composed
`Primrec` theorem already exists in Lean**.

## Evidence and next boundary

`tools/audit_m82_asymmetric_return.py` checks the 15 Schur identities, the fixed chart (4),
the first four moments, and the exact recurrence `A⁴=ξ⁻¹A³`, symbolically in ρ,q,K. It then
checks 13 rational source charts, including β=3, body=bcbc. The latter has Hankel/transition/cut
ranks 7/5/4 and the integerized zero product

```text
CAAACAACCACAACACCAACACAAAC.
```

An auxiliary enumeration checks (3) on all 797,160 raw words of lengths 0 through 11 for
the three bodies bcb, bcbc, bcbb at β=3. This is not the universal semantic proof. The complete
proof is the suffix and finite-period argument above.

The first report's nine-state obstruction remains correct: fixing B,D at times 1,2 and a
common uniform separator row at times 3,4 needs at least nine states, even with arbitrary
zeroth moment and later returns. A nonuniform row at dimension eight must annihilate κ and
η=(K−3V+48,0,0,27−K)ᵀ. Such a nonzero row cannot preserve both members of an accepting
toggle pair. The new row obeys these algebraic constraints and deliberately retains only the
erase-phase member. Thus the two reports are complementary, not contradictory.

The chart's remaining obligations have now been discharged. `ThreeStepRealization` checks
the generic eight-state transition, every return moment, and the nonzero eigenline.
`AsymmetricSeparatorRealization.factor_two`, `factor_one`, and `factor_zero` check (4)
uniformly. `AsymmetricSeparatorRegularity` proves the denominator and role-scale estimates;
`AsymmetricSeparatorMoments` assembles the exact return sequence; `AsymmetricSeparatorTail`
checks the source slope, its code identity, and source-parameter regularity. Their reviewed
transitive dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining formalization has two consumers: the finite wrong-phase exclusion and the
composed primitive-recursive integer endpoint through `SingularReturnFamily` and the existing
source. Do not rebuild generic
Hankel minimization or continue the old uniform-row search. No publication claim, theorem
table cell, or external priority assertion is changed by this audit.
