# Fixed Rank-Two Symmetric-Square Leakage Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `387da0c` on `wave3-m34-ucb`

**Salvage record:** `G3-S07`

## Verdict

A fixed rational rank-two leakage cannot carry a spanning symmetric-square orbit equivariantly
unless the binary generators are elementary: they share a rational projective point or preserve
one algebraic projective pair. This closes the rank-two successor to the full-rank cut `G3-S05`
at its exact fixed-quotient seam.

## Exact Cut

Let `L` be a rational `3×3` matrix of rank two, let `Aᵢ` be invertible rational binary
generators, and let `Hᵢ` be fixed three-state quotient actions. Suppose three binary rays
`u,v,w` have nonzero pairwise cross determinants and satisfy

```text
L Sym²(Aᵢ)ν(r) = HᵢLν(r),    r∈{u,v,w}
```

for every generator. `G3-S04` makes the three Veronese columns a basis. Lean therefore upgrades
the three pointwise equations to `L Sym²(Aᵢ)=HᵢL`. Rank-nullity gives
`ker L=ℚk` for a witnessed `k≠0`, and the intertwiner makes this line invariant under every
`Sym²(Aᵢ)`.

Identify `k=(X,Y,Z)` with `S=[[X,Y],[Y,Z]]`. Lean checks

```text
S(Sym²(A)k)=ASAᵀ.
```

If `det S=0`, rational factorization gives `k=cν(r)` with `c≠0` and `r≠0`; equivariance of `ν`
then makes `r` a common projective fixed point. If `det S≠0`, define

```text
J=[[0,−1],[1,0]],    T=SJ,    δ=−det S.
```

The checked identities are `tr T=0`, `T²=δI`, and

```text
det(A)·AT = λ·TA
```

whenever `Sym²(A)k=λk`. Determinants give `λ²=det(A)²`; over `ℚ`, therefore
`λ=±det(A)`. Since `A` is invertible, cancellation yields `AT=TA` or `AT=−TA`. Over any field
containing a root of `t²−δ`, the first relation preserves each eigenspace of `T` and the second
maps the root eigenspace to the opposite-root eigenspace. Both transport implications are
kernel-checked independently of the rank-two argument.

## Boundary

The theorem needs one fixed leakage, one fixed quotient action per generator, and three
pairwise-distinct source rays on which the quotient equations hold. It does not cover leakage or
quotient maps chosen from the word or source state, a source orbit with at most two rays, rank at
most one, or compatibility known only on a nonspanning carrier. It does not provide a syntax
guard, an orientation for inverse search, a positive-monoid compiler, or a mortality converse.

The phrase “algebraic pair” denotes the two eigendirections after splitting `t²−δ`. The formal
conclusion records the rational normalizer certificate itself: `tr T=0`, `δ≠0`, `T²=δI`, and
commutation or anticommutation for every generator. It does not invoke a hidden classification
theorem.

## Verification

```text
lake build MatrixMortality.SymmetricSquareLeakage
lake build MatrixMortality
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
axiom snapshot: exact match
```

Every publication theorem is listed in `AxiomAudit.lean`. No project axiom, proof aperture,
linter suppression, external declaration, or reference file was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Three distinct Veronese tests force the global leakage intertwiner | promotion | Lean-checked basis cancellation |
| Rank-two leakage has a one-dimensional invariant kernel | promotion | Lean-checked rank-nullity and kernel transport |
| A degenerate invariant tensor gives a common rational ray | promotion | Lean-checked rational Veronese factorization |
| A nondegenerate invariant tensor gives a normalized algebraic pair | promotion | Lean-checked twist identities and commute/anticommute transport |
| Fixed equivariant rank-two leakage supports non-elementary dynamics | rejected | the formalized point/pair bifurcation |
| Rank-one or dynamically varying leakage is impossible | open | outside the hypotheses |
| `M₃(4)` or `M₂(3)` is decided | open | no all-word mortality equivalence follows |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: fixed rank-two leakage with consistent quotient dynamics on a
         spanning Sym² orbit for a non-elementary binary action.
REMAINS: rank at most one, nonspanning orbits, or leakage/quotient dynamics
         varying with the word or source; syntax and mortality converses.
```

## Artifacts

- [`SymmetricSquareLeakage.lean`](../MatrixMortality/SymmetricSquareLeakage.lean)
- [`G3-S07`](../SALVAGE.md#g3-s07-fixed-rank-two-symmetric-square-leakage-is-elementary)
