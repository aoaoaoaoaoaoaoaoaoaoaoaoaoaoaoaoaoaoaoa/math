# Fixed Symmetric-Square Leakage Taxonomy Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `39065e0` on `wave3-m34-ucb`

**Salvage record:** `G3-S09`

## Verdict

Every singular fixed rational Sym² intertwiner is zero or forces elementary binary dynamics. A
dependent image of three distinct Veronese rays with consistent pointwise quotient dynamics
supplies both singularity and the global intertwiner. Combined with the full-rank determinant
cut, this closes all fixed leakage ranks at that exact spanning-equivariance seam.

## Rank-One Cut

Let `L` have rank one and satisfy

```text
L Sym²(Aᵢ)=HᵢL
```

for invertible rational binary generators `Aᵢ`. Transposition makes the one-dimensional range of
`Lᵀ` invariant under `Sym²(Aᵢ)ᵀ`. Lean extracts a witnessed nonzero covector `f` and scalars
`λᵢ` with `f Sym²(Aᵢ)=λᵢf`.

For `f=(p,q,r)`, define

```text
Q(f)=[[p,q/2],[q/2,r]].
```

The checked dual covariance law is

```text
Q(f Sym²(A))=AᵀQ(f)A.
```

If `det Q(f)=0`, the tensor `(p,q/2,r)` factors over `ℚ` as `cν(n)`, where `c≠0` and `n≠0`.
Thus `f(v)=c(n·v)²`. Equivariance preserves its zero set, so the rational ray perpendicular to
`n` is fixed by every generator.

If `det Q(f)≠0`, put `J=[[0,−1],[1,0]]` and `T=JQ(f)`. Lean checks

```text
tr T=0,    T²=−det(Q(f))I,
det(A)·TA=λ·AT.
```

Taking determinants in `AᵀQA=λQ` gives `λ²=det(A)²`. Hence `λ=±det(A)`, and invertibility of
`A` permits exact scalar cancellation: `AT=TA` or `AT=−TA`. Over a splitting field of
`t²+det Q`, the generators therefore preserve or swap the two eigendirections of `T`. This is the
same algebraic-point/pair conclusion as the rank-two kernel theorem, now obtained from the dual
row line.

## Unified Taxonomy

Lean separately proves that rank zero implies `L=0` and that a determinant-zero rational `3×3`
matrix has rank at most two. The public singular-intertwiner theorem splits the remaining ranks:

```text
det L=0  and  L Sym²(Aᵢ)=HᵢL
  ⇒ L=0 or the binary action is elementary.
```

The packaged three-ray theorem assumes three nonzero pairwise cross determinants, pointwise
quotient equations on those rays, and dependence of their leaked images. The Veronese determinant
factorization makes the source columns a basis. Pointwise equations therefore become the global
intertwiner, while determinant multiplicativity forces `det L=0`. The singular theorem then
applies. `G3-S05` rejects the complementary full-rank dependent image.

## Boundary

The spanning hypothesis cannot be inferred from two tests. Lean exhibits the zero map and the
nonzero projector onto the middle Sym² coordinate; they agree on the distinct Veronese axes
`ν(1,0)` and `ν(0,1)`. Thus pointwise quotient equations on at most two rays do not determine a
global three-state action.

`G3-S03` forces the exact terminal fork into a nonzero invariant line or plane. It does not prove
that this carrier contains three distinct underlying binary rays, nor does it supply a global
quotient law for a leakage specified only on its accepted states. If an invertible binary action
really preserves an orbit of at most two projective rays, it is already the invariant-point/pair
elementary case. The live gap is partial, nonspanning compatibility without global equivariance,
or leakage varying with the word or source, not an unclassified fixed rank.

The result supplies no syntax guard, source-uniform compiler, directional inverse law, or
mortality converse. It closes an architecture, not a displayed mortality box.

## Verification

```text
lake build MatrixMortality.SymmetricSquareLeakageTaxonomy
lake build MatrixMortality
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
axiom snapshot: exact match
scripts/check.sh: passed
```

Every publication theorem is listed in `AxiomAudit.lean`. No project axiom, proof aperture,
linter suppression, external declaration, or reference file was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Rank-one fixed leakage yields a common dual Sym² eigenline | promotion | Lean-checked transpose range argument |
| A degenerate dual eigenline gives a common rational ray | promotion | Lean-checked rational square factorization |
| A nondegenerate dual eigenline gives an invariant algebraic pair | promotion | Lean-checked similitude and twist identities |
| Every singular fixed Sym² intertwiner is zero or elementary | promotion | Lean-checked rank trichotomy |
| A dependent equivariant three-ray image is zero or elementary | promotion | Lean-checked spanning and determinant corollary |
| Two pointwise rays suffice to recover global equivariance | rejected | explicit Lean-checked middle-projector witness |
| `G3-S03` automatically supplies three distinct binary rays | open | not implied by its abstract carrier theorem |
| Word-dependent or source-dependent leakage is impossible | open | outside the fixed-intertwiner hypotheses |
| `M₃(4)` or `M₂(3)` is decided | open | no all-word mortality equivalence follows |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: every fixed linear Sym² leakage rank on a spanning orbit with one
         consistent quotient action; rank one is now classified, not merely
         known singular.
REMAINS: nonspanning partial compatibility or leakage/quotient behavior varying
         with the word or source; syntax, reachability, and mortality converses.
```

## Artifacts

- [`SymmetricSquareLeakageTaxonomy.lean`](../MatrixMortality/SymmetricSquareLeakageTaxonomy.lean)
- [`G3-S09`](../SALVAGE.md#g3-s09-fixed-symmetric-square-leakage-taxonomy)
