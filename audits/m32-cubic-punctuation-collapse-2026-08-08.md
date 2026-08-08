# M₃(2) Cubic-Punctuation Collapse Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The nonsplit spectral branch sought a cubic ambient action whose singular returns could serve
as recurrent punctuation while its invertible returns carried unbounded computation. This audit
reconstructs the irreducible-cubic return algebra and checks the pure-cubic collapse in Lean.

The branch does not decide M₃(2). It proves that cubic singular timing cannot carry the
unbounded information: the non-pure case has only finitely many singular cuts, while the pure
case forgets every wait except its residue modulo three.

## Irreducible Cubic Skeleton

Let `A ∈ GL₃(ℚ)` have irreducible characteristic polynomial

```text
f(X)=X³−aX²+bX−N,
```

and let `Mₙ=VAⁿU`, where `U` and `V` have rank two. Identifying `ℚ[A]` with the cubic
field `K=ℚ(θ)`, the sandwich map

```text
z ↦ V m_z U
```

is injective: multiplication by nonzero `z` sends the two-plane `im U` to another two-plane,
which cannot lie in the line `ker V`. Hence every `Mₙ` is nonzero, `M₀,M₁,M₂` are
linearly independent, and every singular return has rank one.

Every nonzero scalar observation `rMₙc` has exact order three. Its `3 × 3` Hankel matrix
factors into the cyclic covectors `rV,rVA,rVA²` and cyclic vectors `Uc,AUc,A²Uc`, both bases
because `f` is irreducible. Applying the same argument to `∧²A` proves that

```text
dₙ=det Mₙ
```

has exact irreducible characteristic polynomial

```text
X³−bX²+aNX−N².
```

## Torsion Dichotomy

A quotient of two cubic roots is a root of unity exactly when

```text
f(X)=X³−N,
```

equivalently `A³=NI`. Indeed, Galois invariance forces all three roots into one quotient
class; comparing the real root with the conjugate pair gives `N=γ³`. Conversely the roots
of a pure cubic differ by cube roots of unity.

If the cubic is not pure, `dₙ` is a nondegenerate order-three rational recurrence. Its zero
set is finite by Skolem–Mahler–Lech and effectively enumerable using the order-at-most-four
Skolem decision procedure already audited from Bacik. Distinct waits also give distinct
projective returns: `Mₙ=λMₘ` would imply `Aⁿ⁻ᵐ=λI` and hence cubic torsion.

If `A³=NI`, then

```text
M_(3q+r)=N^q M_r,   r∈{0,1,2}.
```

Lean proves the corresponding equality for arbitrary return words and, for `N≠0`, the exact
equivalence between physical mortality and mortality of the finite residue triple
`{M₀,M₁,M₂}`.

## Residual Throats

Any minimal zero product has rank-one returns at its two ends and only units inside. An interior
rank-one factor `pℓ` would split the zero outer product and expose a shorter zero subproduct.
Thus the non-pure residue is a finite set of isolated singular endpoints joined by words over an
infinite, projectively injective unit alphabet.

Pure-cubic triples satisfy the rational determinant-polarization identities

```text
N det C₀+Δ(C₁,C₂)=0,
  det C₁+Δ(C₀,C₂)=0,
  det C₂+NΔ(C₀,C₁)=0,
Δ(X,Y)=det(X+Y)−det X−det Y.
```

They follow by expressing the two compression rows through the trace pairing in `ℚ(∛N)`
and taking the determinant of the resulting rank-one tensor. Conversely these equations, with
the explicit rank-two independence condition on the tensor factors, reconstruct the return
triple.

If exactly one residue is singular, the other two units `G,H` obey
`Δ(G,H)=0`, hence `tr(G⁻¹H)=0`; Cayley–Hamilton makes `G⁻¹H` a projective involution.
This leaves one constrained PI₂ instance. With no singular residues the triple is immortal;
with two singular residues mortality is four order-at-most-two scalar recurrence tests.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| cubic-field sandwich faithfulness | promotion | elementary dimension argument; independently reconstructed |
| exact scalar and determinant order three | promotion | cyclic Hankel factorizations independently reconstructed |
| pure cubic is the only torsion case | promotion | Galois and real-embedding proof independently reconstructed |
| non-pure singular times are finite and effective | promotion | depends on the already audited low-order Skolem theorem |
| pure-cubic waits collapse modulo three | formalized | arbitrary-word equivalence checked by Lean |
| determinant-polarization tensor and involutive ratio | promotion | independently expanded and checked algebraically |
| cubic spectrum decides M₃(2) | rejected | both all-unit bridge problems remain open |
| cubic recurrent punctuation carries unbounded memory | rejected | finite isolated cuts or a three-letter residue alphabet |

The field and trace calculations are retained here rather than as a parallel algebraic-number
library. The only theorem that changes the executable reduction boundary is the arbitrary-word
pure-cubic collapse, which is formalized in `CubicReturn.lean`.

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: aperiodic recurrent cubic singular punctuation; non-pure repeated projective controls; unbounded wait memory in pure cubics
REMAINS: isolated non-pure rank-one cuts joined by the true infinite unit alphabet; pure-cubic involutive-ratio PI₂; the split guard and rank-(2,2) trunks
DISTANCE: every cubic spectral attack must now solve an all-invertible projective bridge rather than store computation in singular times
```
