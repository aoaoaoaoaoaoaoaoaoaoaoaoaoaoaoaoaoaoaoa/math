# M₄(3) original semantic-incidence obstruction audit

**Date:** 10 August 2026

**Status:** fixed-boundary complete-block realization obstructed; arbitrary mixed transport open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide whether one complete side-normal Neary block between fixed original
parabolic endpoint rays can realize the terminal equation

## Verdict

The direct semantic realization fails. The original exceptional bridge sends a complete
side-normal correspondence block to an affine `2 × 2` family whose constant, upper-code, and
lower-code coefficients obey one endpoint-independent linear law. The Neary terminal coefficient
violates that law. More strongly, if any fixed endpoint incidence vanishes on the entire formal
terminal plane, it vanishes on the compulsory length plane and hence accepts nonmatches.

Lean also proves that the bridge determinant is negative for every pair of nonempty ternary
words. A nonempty complete Neary block therefore cannot itself be a singular endpoint wall.

This is not global nonincidence. The theorem concerns one intact complete semantic block with
fixed endpoint rays and the formal affine terminal plane. Reachable malformed endpoints,
incomplete gaps, and discrete accidental incidences remain possible. The full original
parabolic transport problem and `M₄(3)` remain open.

## Source Lock

The external report read branch `m43-cube-root-incidence` at
`5cb071fa338f46b484f21764d2df4ba4d2bc0227`. Its transient final report has SHA-256 digest
`129691e64f9f5e0a01944ac238b1da635b1d8587a13a3c80e46b3ad2bf06de2f`.
The six-report salvo was adjudicated before synthesis; this ratchet was reconstructed after the
source-scanner and retuned-boundary siblings had moved the branch to
`402b5aa8442d04c0f788ad68a0ec4b9f899fbcb9`.

## Complete Middle

For upper and lower ternary codes `X,Y` and scales `σ,τ`, the reduced original middle is

```text
M(X,Y,σ,τ) = [[1, X, 2Y],
              [0, σ,  0],
              [0, 0,  τ]].
```

Lean proves that for concrete words this is exactly the fixed conjugate

```text
M = E · sidePcpMatrix(upper,lower) · E⁻¹,

E   = [[1,0,0], [0,0,1], [0,1/2,0]],
E⁻¹ = [[1,0,0], [0,0,2], [0,1,0]].
```

It also evaluates all four physical complete gaps: rule gaps have length three, erasure gaps
have length zero, and each reduced atom is the corresponding `M(X,Y,σ,τ)`. Induction composes an
arbitrary complete Neary tile word to the single semantic middle of its two spelled words.

Using the existing exceptional factors `Kρ(M)=coreInput · M · coreOutput ρ`, direct expansion
gives

```text
det Kρ(M) = (9ρ/2) ·
  [τ(22X+31) - σ(22τ+11Y+9)].
```

For nonempty upper and lower words, nonzero ternary digits give

```text
X < σ,       τ/3 ≤ Y,       3 ≤ σ,τ.
```

These bounds make the bracket strictly negative. Since the Neary morphisms are nonerasing, no
nonempty complete Neary block is a wall.

## Fixed-Incidence Law

For fixed endpoint vectors `a,b`, put

```text
F(X,Y,σ,τ) = a · Kρ(M(X,Y,σ,τ)) · b
           = c₀ + cX·X + cY·Y + cσ·σ + cτ·τ.
```

The exact bridge expansion yields

```text
c₀ = (36ρ-9/4)a₀b₀ + 18a₀b₁,
cX = 9ρa₀b₀,
cY = (57ρ/2-11/4)a₀b₀ + 22a₀b₁,
cσ = (-9ρa₀ + 9ρa₁/4)b₀,
cτ = (57ρ/4-11/8)a₁b₀ + 11a₁b₁.
```

Elimination gives the fixed law

```text
22c₀ - 31cX - 18cY = 0.
```

The paired terminal coefficient `X+mσ-Y` has `(c₀,cX,cY)=(0,1,-1)`, for which the left side is
`-13`. It therefore cannot equal any nonzero scalar multiple of a fixed incidence, even after
adding a multiple of the compulsory length equation `τ-tσ`.

Lean proves the same-zero statement without treating coefficient comparison as an informal
polynomial argument. If

```text
F(X, X+mσ, σ, tσ) = 0    for every X,σ ∈ ℚ,
```

then specialization at `(X,σ)=(0,0),(1,0),(0,1)` and the fixed law force
`c₀=cX=cY=0` and `cσ+t cτ=0`. Hence

```text
F(X,Y,σ,tσ)=0    for every X,Y,σ ∈ ℚ.
```

No fixed pair of rays recognizes the formal terminal equation by its zero set.

## Oriented Survivor

The report also derived a necessary condition for an actual incidence through a genuine terminal
block. With `ρ=3^β`, transform the left-wall row to `a=(a₀,a₁)` and normalize it so that the
smaller 3-adic valuation is zero. If the upper word has length `n`, vanishing requires

```text
ν₃(a₁)-ν₃(a₀) = n+β+1
```

and, after writing `a₁=3^(n+β+1)u`, the leading units must satisfy

```text
u+a₀ = 0  in 𝔽₃.
```

The exact unreduced unit equation remains open. These valuation conditions were independently
checked against the displayed rational bridge expansion but were not retained as a Lean layer:
they guide the surviving arbitrary-transport attack and do not themselves exclude a reachable
wall.

## Claim Disposition

| Claim | Disposition |
| --- | --- |
| Complete semantic-middle conjugacy | formalized |
| Complete original atom and word evaluation | formalized |
| Exact bridge determinant and nonempty negativity | formalized |
| Endpoint-independent coefficient law | formalized inside the same-zero theorem |
| Fixed-ray formal terminal recognition | refuted and formalized |
| Exact 3-adic cylinder and leading unit for a genuine hit | audited; necessary only |
| Original empty punctuation cannot surround a terminal block | audited consequence of the cylinder |
| Global nonincidence for arbitrary mixed bridges | open |
| An actual legal or malformed incidence hit | open |
| `M₄(3)` | open |

## Frontier Cut

Delete complete semantic blocks as endpoint walls and delete all fixed-ray attempts to make one
intact complete block equal the terminal plane. The semantic node survives only through
history-dependent or malformed endpoint geometry, incomplete gaps, or a discrete incidence not
obtained from formal-plane recognition. The oriented node is now exact: decide whether reachable
left walls can enter the depth-`n+β+1` cylinder with the required leading unit and satisfy the
remaining rational equation.

## Artifact

[`MatrixMortality/ParabolicSemanticObstruction.lean`](../MatrixMortality/ParabolicSemanticObstruction.lean)
