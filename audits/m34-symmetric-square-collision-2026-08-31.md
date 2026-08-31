# Symmetric-Square Collision Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `0944bc5` on `wave3-m34-ucb`

**Salvage record:** `G3-S04`

## Verdict

The binary symmetric-square covariant is an exact three-state projective-collision detector,
but not a directional parser or a mortality compiler. Its three-ray determinant also turns the
complete-fork carrier bound into a sharp obstruction: a direct Sym² fork confined to a line or
plane carries at most two projective rays, so it cannot realize non-elementary binary dynamics.

## Exact Representation

For `v=(x,y)`, define

```text
ν(v)=(x²,xy,y²).
```

For `A=[[a,b],[c,d]]`, define

```text
Sym²(A)=
  [[a², 2ab,    b²],
   [ac, ad+bc,  bd],
   [c², 2cd,    d²]].
```

Lean proves over every commutative ring:

```text
Sym²(A)ν(v)=ν(Av),
Sym²(AB)=Sym²(A)Sym²(B),
Sym²(I)=I,
det(Sym²(A))=det(A)³.
```

The multiplication and identity laws are packaged as a monoid homomorphism. Over a field,
`det(A)≠0` implies that `Sym²(A)` has nonzero determinant and rank exactly three. Thus the
construction has an explicit three-coordinate cost and leaves no fourth guard coordinate.

## Tangent Detector

For `u=(p,q)`, let

```text
τᵤ=(q²,−2pq,p²),
Δ(u,v)=u₀v₁−u₁v₀.
```

Direct expansion gives

```text
τᵤν(v)=Δ(u,v)².
```

Lean also proves the equivariance laws

```text
Δ(Au,Av)=det(A)Δ(u,v),
τ_Au ν(Av)=det(A)² τᵤν(v).
```

For integer pairs, the tangent scalar vanishes exactly when `Δ(u,v)=0`. If it does not vanish,
it is an integer square at least one. When both pairs are nonzero, this is exactly collision of
their projective rays. The zero pair must remain excluded by any projective caller.

This gap is algebraic, not directional. Squaring erases the sign of `Δ`; it gives no chamber,
place, or normal-form choice for inverse search.

## Three-Ray Cut

For integer pairs `u,v,w`, Lean proves

```text
det[ν(u) ν(v) ν(w)] = Δ(u,v)Δ(u,w)Δ(v,w).
```

Hence a singular matrix of three Veronese columns contains a colliding pair. More sharply, if
`Δ(u,v)≠0` and the three columns are singular, then `w` collides with `u` or `v`.

Choose any two distinct rays in a Veronese orbit contained in a vector subspace of dimension at
most two. Every third ray forms a singular column triple with them and therefore repeats one of
the first two. The whole orbit contains at most two projective rays.

`G3-S03` independently forces the accepted complete-fork orbit of every exact three-state
`bcbc` recognizer into a one- or two-dimensional carrier, and its invertible fork blocks restrict
to binary projectivities. The factorization above therefore excludes direct non-elementary Sym²
fork blocks. What survives is an invariant point or invariant pair, precisely the elementary
stratum already separated in the dimension-two campaign.

This composition does not exclude a construction with a fixed leakage insertion around Sym².
Such an insertion must provide syntax policing without exceeding three states and must be proved
on the complete raw control monoid.

## Verification

The following checks pass in the isolated worktree:

```text
lake build MatrixMortality.SymmetricSquareCollision
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every publication-facing theorem is listed in `AxiomAudit.lean` and depends only on reviewed
Mathlib axioms. No project axiom, proof aperture, warning suppression, external reference file,
or numerical premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Sym² is a covariant monoid representation with determinant cube | promotion | Lean-checked polynomial identities |
| The tangent scalar is exactly `Δ²` and is equivariant | promotion | Lean-checked polynomial identities |
| Integral noncollision has scalar gap at least one | promotion | Lean-checked integer order theorem |
| A singular Veronese triple contains a colliding pair | promotion | Lean-checked determinant factorization |
| A Veronese orbit in a line or plane has at most two rays | promotion | Lean-checked singular-triple corollary |
| Direct non-elementary Sym² complete-fork blocks survive `G3-S03` | rejected | carrier bound plus two-ray corollary |
| Sym² supplies malformed-word policing or directional pruning | rejected | all three coordinates are occupied and `Δ²` loses sign |
| A leakage-augmented Sym² compiler is impossible | open | no general leakage theorem is proved |
| `M₃(4)` or `M₂(3)` is decided | open | no positive-language reachability theorem follows |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: direct irreducible/non-elementary Sym² complete-fork realizations.
ADDED:   a formal exact three-state projective-collision detector, discrete
         integral gap, and two-ray Veronese-plane theorem.
REMAINS: construct a leakage/syntax mechanism around the detector, or prove
         that every such insertion collapses; directional UCB₂ search remains
         independent.
```

## Artifacts

- [`SymmetricSquareCollision.lean`](../MatrixMortality/SymmetricSquareCollision.lean)
- [`G3-S04`](../SALVAGE.md#g3-s04-symmetric-square-collision-and-fork-obstruction)
