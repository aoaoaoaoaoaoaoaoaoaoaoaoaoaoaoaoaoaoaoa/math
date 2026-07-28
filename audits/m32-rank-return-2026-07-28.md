# `M₃(2)` Rank-and-Return Audit

**Audit date:** 2026-07-28

**Target:** mortality of two `3 × 3` rational or integer matrices

**Inputs:** the public Pro exchange recovered on 2026-07-28, Fable's ReturnSquare report and
checker, the existing mortality corpus, and the stored Skolem references

**Disposition:** contracted into `R32-*` records in `SALVAGE.md`; raw reports remain ephemeral

## Verdict

No decision procedure or undecidability reduction for `M₃(2)` was obtained.

The accepted material divides the cell into two exact residues:

```text
rank (2,2): constrained products in a two-vertex square of 2 × 2 edges;
rank (3,2): products of the return recurrence M_n=VAⁿU.
```

The rank-`(3,2)` reduction is the new central object. ReturnSquare is a fully checked laboratory
inside it, but large parameter regions are now proved immortal and the surviving zeros require
at least three positive returns.

## Claim Audit

| Claim from the reports | Audit result | Durable status |
| --- | --- | --- |
| A unit plus a split finite-rank cut reduces exactly to return products `VAⁿU` | Correct and generalized beyond dimension three | Lean: `ReturnFamily.pairGenerator_isMortal_iff` |
| Two split rank-two generators reduce exactly to adjacent `2 × 2` edge products | Correct and generalized to arbitrary split finite-rank families | Lean: `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero` |
| Four compatible edges can be pushed out to two rank-two `3 × 3` generators | Correct after stating the shared-line compatibility and split-edge hypotheses | Lean: `TwoPlaneEdges.*` |
| Every rank-one profile is decidable | Correct; endpoint collapses and scalar returns are order-at-most-three LRS | Audited; Skolem decision theorem imported from Bacik |
| The rank-`(2,2)` profile is equivalent to the full `M₂(3)` hard core | Too strong | Rejected; only exact constrained-edge reduction and a generic reverse embedding are retained |
| The generic reverse embedding works when `αβ≠0` | Algebraically correct | Audited as `R32-M01`; basis adaptation and all-path theorem remain unformalized |
| The two degenerate source points give a finite Turing reduction | Plausible but underspecified as a many-one compiler | Not promoted |
| ReturnSquare has ranks `(3,2)` for every swept parameter | False at `c=−1` | Corrected: `B²=0` and `rank B=1` at `c=−1` |
| The finite ReturnSquare sweep found only immortal instances | False because the sweep failed to exclude `c=−1` | Rejected; five reported cases were immediate mortal instances |
| ReturnSquare has the displayed return matrix and projective rail | Correct | Lean: `ReturnSquare.returnMatrix_eq_transfer` and projective identities |
| One-return zeros are explicit resonances | Correct | Lean: `positiveBridge_singleton` |
| Two positive returns never vanish for rational `c` and integral scales at least two | Correct; the discriminant lies in a two-square cage and parity excludes the middle square | Lean: `twoReturnDiscriminant_not_isSquare`, `positiveBridge_pair_ne_zero` |
| Literal reversible push/pop fits in three states | False for the proposed exact return series | Lean lower bound: `ReturnSquareTax.reversibleStack_card_lower_bound` |
| A third singular spectral mode can repair reversible push/pop | False for exact quadratic pencils | Lean: `ReturnSquareNoGo.threeMode_swap_eq_zero` |
| Two exact push verifiers can distinguish the intended rail | False: coefficient comparison forces blind scaling | Lean: `ReturnSquareNoGo.verifiedPush_eq_blindScale` |
| `c>0` is immortal | Correct but not sharp | Strengthened to `c≥0` in Lean |
| A negative interval trap exists | Correct | Strengthened to a homogeneous, sign-invariant, pole-free double-cone theorem and full mortality wall |
| The outer negative wall is `d>1+(q−1)/q²` for `c=−d` | Correct as a sufficient uniform condition | Lean: `not_physical_isMortal_of_beyond_negative_wall` |
| A `q`-adic attractor or Zariski-density argument settles the remaining strip | Unsupported | Rejected |
| Finite quotient survival supplies positive evidence | Only computationally | The one-sided no-certificate theorem is formalized; no local-global converse is claimed |

## Formalized Core

### Split returns

For a unit `A` and a cut `B=UV` with split `U,V`, every physical word either contains no `B`
and is a unit, or fractures into a product

```text
U (VA^n₁U)⋯(VA^nₖU) V.
```

The exterior splittings reflect zero. Empty runs, leading and trailing powers, and repeated cuts
are included. A finite block-Hankel section of `n ↦ VAⁿU` factors through any exact ambient
realization.

### Split edge squares

For `Aᵢ=UᵢVᵢ`, put `Cᵢⱼ=VᵢUⱼ`. Every nonempty word is zero exactly when its constrained
adjacent-edge product is zero. Conversely, two coordinate planes sharing `e₀` realize any four
edges satisfying

```text
Cᵢ₀e₀=Cᵢ₁e₀.
```

One split incoming edge per target gives an explicit right inverse and proves both ambient
generators have rank two. This formalizes the geometric pushout without erasing its path
language.

### ReturnSquare

For

```text
A=diag(1,q,q²),
U=[[1,0],[0,1],[1,0]],
V=[[-1,1,c+1],[c,1,0]],
```

the return is

```text
T_c(t)=[[(c+1)t²−1,t],[c,t]],       t=qⁿ.
```

The zero-wait return is `[1,1]ᵀ[c,1]`. Positive returns are units when `q≥2` and `c≠−1`, so
physical mortality is precisely a scalar bridge between two copies of this internal
punctuation.

The two-return coefficient has a quadratic core in `c`. Its integer discriminant lies strictly
between `N²` and `(N+2)²`; an explicit odd gap excludes `(N+1)²`. No rational `c` kills two
positive returns.

### Projective double cone

For `c=−d`, write

```text
s_d(t)=(d−1)t²+1,
Φ_t(z)=(t−s_d(t)z)/(t−dz),
β=q/s_d(q).
```

Under

```text
q≥2,      t≥q,      d>1+(q−1)/q²,
```

the interval `(0,β]` is backward invariant under `Φ_t`. The formal mortality proof uses its
homogeneous lift

```text
(0<x, 0<y, x≤βy)  or  (x<0, y<0, βy≤x),
```

so no denominator or orientation case is hidden. A pulled-back target ray lies in this double
cone; induction through the return word would trap `[1,1]`, contradicting `β<1`.

## Unformalized Boundary

1. The generic reverse compiler needs explicit adapted bases, a normal form for every edge path
   between rank-one loops, and a precise treatment of `αβ=0`.
2. Rank-one-profile decidability imports Bacik's Skolem theorem; no executable Lean algorithm is
   present.
3. The remaining ReturnSquare strip

   ```text
   −(1+(q−1)/q²) ≤ c < 0
   ```

   contains the one-return resonances and an unclassified length-at-least-three residue.
4. The reported cyclotomic and `q`-adic observations have algebraic kernels but no complete
   word-level theorem.
5. The proposed irreducible-cubic and two-scale return pencils remain research directions, not
   claims.

## Operational Consequence

Searches for `M₃(2)` should begin from one of two typed objects:

```text
Compatible two-plane edge square;
Third-order matrix-valued return recurrence n ↦ VAⁿU.
```

The first should be compared directly with the `M₂(3)` projective-incidence ledger. The second
should be attacked by internal low-rank returns, block-Hankel rank, finite quotients, and
homogeneous real or `p`-adic invariant cones. Raw binary-word encodings are downstream
projections of these objects and should not be searched independently.
