# M₄(3) one-sided wall-orbit audit

**Date:** 11 August 2026

**Status:** all-word parabolic incidence reduced to one exterior point-to-ray orbit problem

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** classify every consecutive-wall zero left open by `M4-S06`

## Verdict

The report does not prove mortality or immortality. It replaces the two-sided language of wall
bridges by one exact one-sided projective reachability problem in the already checked exterior
representation.

For a regular wall middle `M`, the repository already supplied the nonzero left cokernel

```text
λ(M)=(v(M),-4w(M)).
```

The dual canonical right kernel is

```text
κρ(M)=Lρ adj(M) k,
```

where `Lρ` retracts the exceptional output factor and `k=(4,4,-1)`. Lean now proves that this
vector is nonzero on every regular wall word and that the corresponding bridge kills it. For
wall endpoints `U,V` and invertible two-dimensional transport `T`, direct rank-one algebra gives

```text
K(U) T K(V)=0  ↔  λ(V) adj(T) κρ(U)=0.
```

If `ξ=adj(T)κρ(U)=(a,b)`, the same equation absorbs both the right-wall condition and the
incidence:

```text
K(U) T K(V)=0  ↔  exteriorState(V) ∼ (0,4b,a).
```

Consequently the pinned three-generator family is mortal exactly when one regular left wall and
one invertible bridge transport generate a projective ray reached by the exterior orbit of a
regular right word. No right-wall grammar, choice of outer factors, or collective cancellation
remains.

## Source Lock

The external attack read branch `m43-cube-root-incidence` at
`2e06706c872a14fb9a02246a16709314561c741e`. Its final-report SHA-256 digest is
`bef3d7b65283da35497a3a82517a60042b650009e09ec4a6b96e85d9891b72c8`.

The displayed coordinate identities, null-vector arguments, rank-one incidence, sum-of-squares
criterion, and arbitrary-literal-word reconstruction were checked independently against
`ParabolicBlade.lean`, `ParabolicDefect.lean`, and `ParabolicExterior.lean`. The new Lean module
checks the canonical right kernel and its nonvanishing; the final projective equivalence remains
audited rather than promoted to a publication theorem.

## Canonical Kernel

Write the exceptional atom as `R=AB`, with `A=coreOutput ρ`, `B=coreInput`, and let
`L=coreLeftInverse ρ`. The fixed projections are

```text
LA=I₂,
AL=I₃-(1/22) e₁ nᵀ,
n=(22,-31,-36),
Bk=0.
```

For `x=adj(M)k`, the wall equation is `nᵀx=0`. Hence `ALx=x`, so

```text
Aκρ(M)=adj(M)k,
K(M)κρ(M)=BM adj(M)k=det(M)Bk=0.
```

If `M` is invertible, `κρ(M)=0` would force `adj(M)k=0` and then `det(M)k=0`, impossible.
The formal file proves these identities without assuming that `M` is a word until the final
regular-word nonvanishing theorem.

## Exact Incidence

The dual left calculation from `M4-S06` gives

```text
λ(M)K(M)=0,    λ(M)=(v(M),-4w(M)).
```

Both endpoint bridges are nonzero rank-one matrices. For any invertible `T`, their product is
zero exactly when the image line of `K(V)` equals the inverse image under `T` of the kernel line
of `K(U)`. In two dimensions, `T⁻¹` is projectively `adj(T)`, which yields

```text
λ(V) adj(T) κρ(U)=0.
```

This statement is independent of outer-factor normalizations and remains valid for empty regular
endpoint blocks.

For arbitrary regular `U,V`, set `adj(T)κρ(U)=(a,b)`. The single rational equation

```text
Fρ(U,T,V)
 = wallDual(U)² + u(V)² + (a v(V)-4b w(V))²
```

vanishes exactly when the bridge product vanishes. Here `wallDual(U)=0` is the same wall
condition expressed in the right-multiplication dual exterior coordinates. Since rational sums
of squares vanish termwise, this is only a terminal conjunction of three exact equations; it is
not a propagated quadratic invariant and does not revive the rejected primal/exterior conic
argument.

## Literal Converse

`M4-S06` already proves that every zero exceptional chain has a consecutive pair of rank-one
walls separated only by invertible bridges. Conversely, a solution of the displayed incidence
expands to the literal reduced word

```text
R U R M₁ R ... R M_s R V R,
```

where `T=K(M₁)...K(M_s)`. Empty endpoint blocks and empty transport are allowed. Existing
factor retractions show that the reduced bridge product is zero exactly when this physical word
is zero; individual denominator clearing preserves the equivalence.

## Master Consequence

The all-word node is now exterior collision avoidance: prove uniformly that no regular exterior
orbit reaches the explicit ray generated from a left wall and an invertible bridge transport, or
exhibit one reach and obtain an exact zero word. The safe flag and defect skeleton restrictions
remain useful sieves, but two-sided wall enumeration is obsolete.

