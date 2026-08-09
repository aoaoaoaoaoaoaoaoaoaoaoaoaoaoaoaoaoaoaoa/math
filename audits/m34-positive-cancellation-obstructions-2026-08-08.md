# Positive-Cancellation Obstruction Audit

**Date:** 2026-08-08  
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `8ffb49a4dc38110e62381cf9d173b23b947d34cf` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a77e25f-6a20-83ea-80e0-75e2daf3294d  
**Primary source:** [Carvalho 2026](../references/carvalho-2026-free-group-pcp.md), arXiv v2 preprint

## Verdict

The finite-state/singular spelling architecture is closed. A cancellative lift with finite fibres
pumps every positive semantic identity loop. A singular one-coordinate extension of a
two-dimensional invertible cancellation quotient does worse: after the singular prefix, every
later quotient-identity factor is exactly absorbed by the complete matrix product. A standalone
same-zero detector for triangle-irreducible positive spellings requires at least six states.

These obstructions do not kill free cancellation. Direct inspection of Carvalho's retained v2
preprint yields a sharper quotient-invariant target:

```text
C halts  ↔  ∃u, g(u)=h(u) and κ(u)=1,
```

where `κ` is the `p`-exponent sum after the injective equalizer map. The affine slice excludes the
identity and selects the oriented primitive accepting loop. A successor need not recognize one
irreducible positive spelling; it may quotient away every identity padding.

## Finite-Fibre Pumping

Let an injective transition `T:X→X` project to a semantic transition `A:Y→Y`. If `A(y)=y` and the
fibre over `y` is finite, every point `ξ` in that fibre satisfies

```text
T^k(ξ)=ξ
```

for some `k>0`. All iterates remain in the fibre, two collide, and injectivity cancels their common
prefix. Lean proves this without a product decomposition of `X`: the finite spelling state may be
twisted arbitrarily over the semantic state.

Applied to the positive cover

```text
x↦x,  y↦y,  z↦y⁻¹x⁻¹,
```

the nonempty words `xyz`, `yzx`, and `zxy` are semantic identity loops. Any finite-fibre
cancellative target overlap eventually identifies `r^k w` with `w`. It cannot make wrong-time
identity insertion permanently illegal. Ordinary GPCP discrepancy updates are bijections in the
free-group completion, so a finite spelling component inside cancellative overlap falls under the
theorem.

## Singular Absorption

Let `q:V→W` have one-dimensional kernel, let a singular map `P:V→V` lift an injective quotient
action `ρ`, and let `R:V→V` act as the identity on the quotient:

```text
qP=ρq,       qR=q.
```

Lean proves `ker P⊆ker q`; singularity and `dim ker q=1` force equality. Since
`im(R−I)⊆ker q=ker P`,

```text
PR=P.
```

Thus a singular prefix retaining a two-dimensional invertible cancellation quotient erases every
later quotient-identity factor as an equality of complete linear maps. No boundary row or column
can recover it. This closes transient singular guards coupled to the proposed persistent
Carvalho quotient. It does not cover an everywhere-invertible infinite fibre or a construction
whose persistent semantics are themselves singular.

## Rank-Six Syntax Wall

Let `N` be the positive words containing none of `xyz`, `yzx`, and `zxy`. If a scalar linear
representation has zero language exactly `N`, take prefixes and suffixes

```text
x, y, z, xy, yz, zx.
```

Their `6×6` coefficient table has support

```text
0 0 0 0 * 0
0 0 0 0 0 *
0 0 0 * 0 0
0 0 * 0 0 *
* 0 0 * 0 0
0 * 0 0 * 0.
```

Columns `x,y,z` first isolate rows `yz,zx,xy`; columns `yz,zx,xy` then isolate rows `x,y,z`.
Lean proves the six rows independent over every field and proves that every row-column
factorization of this table has at least six states. Legality therefore cannot be fused as a
standalone three-state same-zero guard. A halting-specific coupled zero language may have smaller
rank and remains outside the certificate.

## Exponent-One Equalizer Slice

Carvalho defines `χ:F_A→ℤ` by `χ(p)=1` and zero on every other generator. Equation (4) proves that
numbered-state transitions preserve discrepancy `χ`; the simulation starts at `d₀=w₀p`, so every
deterministic discrepancy contains `p`-exponent one. In a halting instance, Proposition 3.2 and
Theorem 3.6 construct a fixed loop conjugate to the marker word `D`, which contains exactly one
`p`. Hence the loop has `χ=1`.

Conversely, any fixed point with `χ=1` is nontrivial, and Theorem 3.6 makes existence of a
nontrivial fixed point equivalent to cyclic-tag halting. In Theorem 4.1, the injective homomorphism
`h:F_Y→F_A` identifies `F_Y` with the closed-path subgroup and carries `Eq(g,h)` exactly to the
fixed loops. With `κ=χ∘h`, therefore,

```text
C halts  ↔  ∃u∈F_Y, g(u)=h(u) ∧ κ(u)=1.
```

This sharpening is derived from the construction rather than stated in the preprint. It is
source-audited, not Lean-reconstructed. It avoids the earlier boundary-square collapse because
`κ(u^n)=n`; only exponent one is accepted.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Injective dynamics on a finite invariant fibre pump an identity loop | promotion | Lean theorem `finiteFibre_identity_pumps` |
| A singular one-coordinate lift absorbs every quotient identity | promotion | Lean theorems `singularLift_kernel_eq_quotientKernel`, `singularLift_absorbs_quotientIdentity` |
| The triangle-irreducible zero support needs six states | promotion | Lean theorem `six_le_card_of_forbiddenTripleSupport` |
| Carvalho halting is equivalent to an exponent-one equalizer witness | promotion | audited derivation from Proposition 3.2 and Theorems 3.6, 4.1 |
| Every positive-cancellation compiler is impossible | rejected | everywhere-invertible infinite fibres and nonquotient semantics survive |
| The exponent-one slice is already classical `GPCP(3)` | rejected | no three-positive-letter affine-slice compiler is supplied |
| `M₃(4)` follows | rejected | no three-control same-zero family is constructed |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: finite-fibre cancellative spelling lifts; singular one-coordinate guards over an
         invertible cancellation quotient; standalone three-state triangle-normal-form guards.
ADDED: Carvalho's exact exponent-one equalizer slice as the positive cancellation target.
REMAINS: compile g(u)=h(u), κ(u)=1 through three positive controls using an everywhere-invertible
         unbounded cocycle, or abandon the persistent two-dimensional group quotient.
```

## Artifact

- [`PositiveFreeCancellation.lean`](../MatrixMortality/PositiveFreeCancellation.lean)
