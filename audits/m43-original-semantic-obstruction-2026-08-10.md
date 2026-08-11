# M₄(3) original semantic-endpoint audit

**Date:** 10–11 August 2026

**Status:** four-parameter endpoint compiler defeated; broader original incidence open

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** decide whether the original parabolic consecutive-wall incidence can realize the
Neary terminal language

## Verdict

The delayed semantic report exposed a terminal-code convention error in the preceding transport
report and the first version of this audit. The repository uses the usual left-to-right ternary
value

```text
code(x ++ y) = 3^|y| code(x) + code(y).
```

For marker value `m=(5ρ−1)/2` and marker scale `t=3ρ`, the actual terminal plane is therefore

```text
Y=tX+m,       τ=tσ,
```

not `Y=X+mσ`. The former depth-`n+β+1` cylinder and its unit equation were derived after the
wrong substitution and are withdrawn.

The fixed-ray formal-plane obstruction survives by a corrected calculation. Formalization also
proves an exact conditional compiler: if two regular mixed-gap contexts reach two explicit
projective rays, one semantic bridge followed by the empty bridge vanishes exactly when its four
side-normal parameters satisfy the Neary terminal equation.

That compiler is not a sound reduction. At `(β,body)=(3,bbcc)`, the lawful source cycles forever,
but one regular gap-thirty `b` atom realizes an extra pseudo-production. An explicit 33-tile word
then satisfies the corrected terminal equation. If the two endpoint contexts do not exist, the
forward compiler is absent; if they exist, this malformed middle produces a zero on the
nonhalting instance. Thus `M4-C04` survives as an exact semantic identity but is parked as a
route to the master problem.

This does not close `M₄(3)`, classify all original-family zeros, or exclude a syntax-sensitive
incidence that remembers more than the four side-normal parameters.

## Source Lock

Both external attacks read branch `m43-cube-root-incidence` at
`5cb071fa338f46b484f21764d2df4ba4d2bc0227`.

- The original transport report has final-report SHA-256 digest
  `129691e64f9f5e0a01944ac238b1da635b1d8587a13a3c80e46b3ad2bf06de2f`.
  Its complete-middle and bridge calculations survive; its terminal substitution and every
  dependent cylinder claim do not.
- The delayed semantic report has final-report SHA-256 digest
  `397d1cad7211146259a7c8224c6e9fa68632585b92596808d0dff580701bccc3`.
  It supplied the corrected convention, forced endpoint rays, conditional zero word, and
  complete-gap endpoint obstructions.

The first report had already moved the branch to
`0bd22487a8969cadee8fe91c71c97cd1f085c6dc` before the delayed report returned. This audit
records the corrective reconstruction from that pushed boundary.

- The pseudo-terminal attack has final-report SHA-256 digest
  `6aaf849c3c9e9d9ff129fb0632d4648ce0be09c2623785bdc28f9204518e79bb`.
  It was reconstructed against the semantically corrected branch boundary
  `c656107678ad3bb48ba0b558139e976d2fb1c7fb`. Its gap-thirty transfer and losing fork are
  formalized below.

## Complete Middle

For upper and lower ternary codes `X,Y` and scales `σ,τ`, the reduced original middle is

```text
N(X,Y,σ,τ) = [[1, X, 2Y],
              [0, σ,  0],
              [0, 0,  τ]].
```

Lean proves that every original rule gap of length three and erasure gap of length zero evaluates
to this matrix, that arbitrary complete tile words compose into one such middle, and that it is a
fixed conjugate of `sidePcpMatrix`.

The exceptional bridge determinant is

```text
det Kρ(N) = (9ρ/2)
  [τ(22X+31) − σ(22τ+11Y+9)].
```

It is strictly negative for every nonempty complete Neary word. A complete word cannot itself be
a wall; this result is independent of the corrected terminal convention.

## Correct Fixed-Ray Obstruction

Every incidence between fixed endpoint rays through `N` is affine:

```text
F(X,Y,σ,τ)=c₀+cX·X+cY·Y+cσ·σ+cτ·τ,
```

with the endpoint-independent coefficient law

```text
22c₀−31cX−18cY=0.
```

If `F` vanishes on the actual formal terminal plane `Y=tX+m, τ=tσ`, coefficient comparison gives

```text
c₀+m cY=0,
cX+t cY=0,
cσ+t cτ=0.
```

Substitution into the fixed law yields

```text
(31t−22m−18)cY = (38ρ−7)cY = 0.
```

Since `ρ=3^β`, the factor is positive. Hence `c₀=cX=cY=0` and
`F` vanishes on the entire length plane `τ=tσ`. Lean proves this generic affine-plane theorem
and its concrete Neary corollary.

The quantifier matters. This rules out formal-plane recognition and exact polynomial identities
of this fixed-ray form. It does not prove that the discrete set of genuine terminal encodings is
Zariski dense, so it does not exclude every possible discrete same-zero coincidence.

The delayed report gives a concrete false positive for the surviving pure length test. If
`E=|tagEncodeβ(body)|`, then

```text
ω=(rule c)^(β+1) (erase b)^(E+1)
```

has `τ=tσ` but is not terminal: its lower spelling contains an internal positive zero-run of
length one, impossible in a tag encoding plus marker when `β>2`. This discrete witness was
audited but was not retained as a separate Lean layer.

## Conditional Compiler

Put

```text
u* = (0,−2,1)ᵀ,                      k = (4,4,−1)ᵀ,
p  = (18,11)ᵀ,
c* = (m,t,−1/2)ᵀ.
```

Here `k` spans the kernel of the exceptional input factor and `p` is the column of the empty
rank-one bridge. A terminal semantic middle satisfies

```text
N c* ∼ u*.
```

Lean proves the following exact seam. Let `C,D` be three-dimensional contexts, let `C⁻¹` be any
left inverse of `C`, and suppose nonzero scalars `λ,μ` satisfy

```text
C u* = λk,
D A p = μc*.
```

Then

```text
Kρ(C N(upper,lower) D) Kρ(I) = 0
  ↔ upper ++ nearyMarker β = lower.
```

The existing exceptional-chain contraction turns this bridge identity into the reduced literal
word `R(CND)RR`. The identity is exact, but it recognizes the side-normal terminal equation
without certifying that the middle encodes a lawful source history.

Formalization also proves that neither target can be reached by a complete semantic context.
On the left, `N u*∼k` would force a ratio of powers of three to equal two. On the right,
`N A p` has positive second and third coordinates, whereas `c*` has opposite signs there.
Both contexts must contain genuinely incomplete gaps.

## Original Pseudo-Terminal Poison

Set `β=3`, `ρ=27`, `body=bbcc`, `m=67`, and `t=81`. The lawful restricted tag orbit is

```text
ccb → bbccb → cbb → bbccb → ⋯,
```

so the source has no terminal word. The original gap-thirty atom is nevertheless

```text
Q(b,30)=N(203,241,243,243),
203=[10001]₃,   241=[11110]₃.
```

It therefore acts as the malformed side-normal pair `10001/11110`. Insert this atom into the
explicit 33-tile pseudo word already used by the retuned obstruction. Its concatenated spellings
`U,V` obey

```text
V=U ++ 1000,   |U|=113,   |V|=117,
```

and hence

```text
Y=81X+67,   τ=81σ.
```

Every label in the middle is regular: the word contains `(b,30)` but not the unique singular
label `(b,1)`. Lean composes the original atom semantics and proves that for every proposed
endpoint pair satisfying the conditional compiler hypotheses, this middle gives an exceptional
chain equal to zero. The same theorem simultaneously proves that the lawful source has no
terminal word.

This is not a failed search for the endpoint contexts. It is a losing fork valid for every
instantiation of them. Any endpoint geometry factoring only through `(X,Y,σ,τ)` accepts the
pseudo-terminal because those parameters contain no certificate of lawful history.

## Forced Determinant Rays

The delayed report additionally classifies exact determinant identities. If fixed contexts make
`det Kρ(CND)` a nonzero multiple of the cross-multiplied terminal polynomial, coefficient
comparison forces

```text
C u* ∼ k,
Dᵀ v* ∼ n,

v*=(t,−m,0)ᵀ,       n=(22,−31,−36)ᵀ.
```

This uniqueness calculation and its Cauchy-Binet derivation were independently checked but not
retained as another formal layer. The weaker right equation `D A p∼c*` feeds the checked
conditional compiler. Neither reachability problem remains a master-path target after the
pseudo-terminal obstruction.

## Withdrawn Cylinder

The former claims

```text
ν₃(a₁)−ν₃(a₀)=n+β+1
```

and the associated leading-unit and unreduced equations used the false relation `Y=X+mσ`.
They have no evidentiary standing. Any oriented arithmetic attack must be re-derived from
`Y=tX+m` or, preferably, attack the exact mixed-gap ray equations directly.

## Claim Disposition

| Claim | Disposition |
| --- | --- |
| Complete original atom and word evaluation | formalized |
| Complete-middle conjugacy and bridge determinant | formalized |
| Negative determinant for every nonempty complete word | formalized |
| Correct actual terminal plane `Y=tX+m, τ=tσ` | reconstructed |
| Fixed-ray formal-plane recognition | obstructed and formalized |
| Fixed-ray recognition only on the discrete code locus | open |
| Conditional mixed-gap endpoint identity | formalized |
| Complete-gap attainment of either compiler endpoint | obstructed and formalized |
| Gap-thirty pseudo-terminal on an admissible no-instance | obstruction formalized |
| Conditional endpoint compiler as a uniform reduction | rejected |
| Forced determinant rays | audited |
| Uniform malformed witness for the pure length test | audited |
| Former depth-`n+β+1` cylinder | rejected |
| Mixed-gap endpoint reachability | no longer a master-path target |
| All-word original-family classification | open |
| Syntax-sensitive semantic incidence | open |
| `M₄(3)` | open |

## Frontier Cut

Delete the false cylinder, complete-gap endpoint contexts, fixed-ray formal-plane identities,
and the four-parameter endpoint compiler as a reduction. Do not spend master-path effort reaching
its two rays: success activates the explicit false zero. The original family remains live only
through an all-word classification of arbitrary consecutive wall incidences, or a genuinely
syntax-sensitive construction whose state excludes pseudo-terminals rather than merely restating
`Y=tX+m, τ=tσ`.

## Artifact

[`MatrixMortality/ParabolicSemanticObstruction.lean`](../MatrixMortality/ParabolicSemanticObstruction.lean)
and
[`MatrixMortality/ParabolicRetunedObstruction.lean`](../MatrixMortality/ParabolicRetunedObstruction.lean)
