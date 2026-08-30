# Singular Triangle-Carrier Collapse Audit

**Date:** 2026-08-30
**Author and auditor:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `345169d`
**Formal owner:**
[`PositiveFreeCancellation.lean`](../MatrixMortality/PositiveFreeCancellation.lean)

## Verdict

There is no separate singular spelling-sensitive branch for a three-state scalar recognizer on
the positive triangle cover. Let `π:S*→G` be positively surjective, let `L⊆G` be recognized by

```text
λ M_w γ = 0  ⇔  π(w)∈L,
```

and suppose `L` omits one known group element. If a positive semantic-identity word `r` has a
singular transition `P=M_r` on a rational three-dimensional carrier, then the same zero language
has an exact realization on `ℚ²` in which every letter acts invertibly. The realization includes
the empty word. If `L` is empty, a fixed identity action with a permanently nonzero coefficient
supplies the two-state realization.

For the triangle cover, `r=xyz` and `π(r)=1`. A singular letter makes `XYZ` singular. Hence every
rational three-state saturated recognizer satisfies the formal dichotomy

```text
all X,Y,Z are invertible
or
the same zero language is recognized by three invertible 2×2 rational transitions.
```

This is a dimension collapse, not an impossibility theorem. It expands the Carvalho leaf into
the dimension-two/projective campaign and removes singularity as an independent source of
spelling memory.

## Rank-One Guillotine

Every finite-dimensional endomorphism of rank at most one factors as

```text
P = v φ
```

for a vector `v` and a linear functional `φ`. If `r` is a semantic identity, then for arbitrary
positive words `u,v`,

```text
λ M_u P M_v γ = (λ M_u v)(φ M_v γ).
```

The zero predicate is therefore a union of a left-spelling predicate and a right-spelling
predicate. Positive surjectivity makes such a group-saturated rectangular language trivial. If
one group value is rejected, it must be empty. Lean proves the arbitrary-spelling rectangular
lemma, the rank-one factorization, and this semantic-identity consequence.

It follows that every semantic identity loop for a nonempty, nonuniversal saturated language
has rank at least two. A singular identity loop in dimension three consequently has rank exactly
two.

## Exact Two-State Carrier

Put `U=im P`, so `dim U=2`, and define the sandwich transition

```text
A_s : U→U,       A_s(u)=P M_s u.
```

Every `A_s` is invertible. Otherwise `rank A_s≤1`. Choose a positive spelling `v` of
`π(s)⁻¹`. The semantic identity loop

```text
r s r v r
```

then factors through `A_s` and has rank at most one, so the rank-one guillotine would make `L`
trivial. This contradicts one accepted and one rejected group value. The empty-language branch
is handled separately by the fixed two-state realization.

Take

```text
γ̅=Pγ ∈ U,       λ̅=λ|U.
```

For `w=s₁⋯ sₙ`, induction gives

```text
A_w γ̅ = M_{r s₁ r ⋯ sₙ r}γ.
```

The formula also holds for `w=ε`: its right side is `M_rγ=Pγ`. Since inserting `r` does not
change the group value, `λ̅A_wγ̅=0 ⇔ π(w)∈L` for every word, including the empty word.
No assumption that `γ`, `λ`, or the empty-word coefficient is nonzero is hidden; nontriviality
forces what the proof needs, while the empty language uses an explicit nonzero model.

Lean first constructs the canonical carrier `U`. Over `ℚ`, it then chooses a basis
`U≃ℚ^(Fin 2)`, conjugates every `A_s`, and transports the seed and boundary to literal two-state
coordinates.

## Triangle Effectivity Over ℚ

The abstract Lean theorem uses surjectivity to choose positive inverse spellings; surjectivity
alone is not algorithmic. The following extraction is uniform when a positive inverse-spelling
section is effective, as it is for the finite triangle cover, and does not ask whether `L` is
nonempty.

1. Compute `P=M_r` and a rational row-reduced basis of `im P`.
2. If `rank P≤1`, the rank-one theorem and the supplied rejected value prove `L=∅`; emit the
   fixed identity two-state empty-language model.
3. If `rank P=2`, compute the three sandwich matrices in the image basis.
4. If one sandwich is singular, the displayed inverse-spelling loop is an effective rank-one
   semantic identity; again emit the fixed empty-language model.
5. Otherwise output the three sandwich matrices, `Pγ` in the image basis, and `λ|im P` in the
   dual basis.

For the triangle alphabet, inverse spellings are fixed:

```text
x⁻¹=yz,       y⁻¹=zx,       z⁻¹=xy.
```

Thus Gaussian elimination and rational matrix arithmetic perform the whole construction. The
Lean theorem states exact existence and coordinate transport; this audit records the extracted
algorithm.

## Singleton-Fibre Sharpening

Apply [`G3-O22`](../SALVAGE.md#g3-o22-invertible-fibre-span-rigidity) to the resulting
two-dimensional invertible carrier. All positive spelling-fibre spans

```text
C_g = span { A_wγ̅ : π(w)=g }
```

have the same dimension. For a nontrivial language, an accepted fibre lies in the one-dimensional
kernel of `λ̅`, so every `C_g` is a line. Let

```text
H={h∈G : C_h=C_1}.
```

Exact fibre transport proves that `H` is a subgroup and that, for any accepted `q`,

```text
L=qH.
```

Carvalho's exponent-one yes-language is a singleton in the semantic group. In a yes-instance its
audited equalizer is `⟨u⟩` with `κ(u)=1`, so `κ(uⁿ)=n` and the exponent-one slice is exactly
`{u}`; in a no-instance the trivial equalizer has empty exponent-one slice. The transported
Nielsen-Schreier map into the triangle semantic group is injective, so it preserves this
empty-or-singleton alternative. Hence any two-state realization of a yes-instance has `H={1}`.
Since the semantic group is `F₂`, its infinitely many distinct fibre rays force the induced
projective action to be faithful. Three such rays also force

```text
[A_z]=[A_y]⁻¹[A_x]⁻¹  in PGL₂(ℚ).
```

The third positive control is therefore a projective inverse composite. This is a two-generator
**group** orbit, not a two-generator positive-semigroup orbit.

For this `F₂` singleton branch, if two positive words have the same semantic value, their reduced
operators are nonzero scalar multiples of one another: they induce projectivities agreeing on
the infinite free orbit. All residual spelling dependence after one identity interleave is
therefore a central projective cocycle, which cannot change scalar vanishing. The discarded
singular coordinate carries no zero-relevant spelling memory.

This gives an effective promised-instance sieve. Put `P=XYZ` and `U=im P`. If the
empty-or-singleton language is nonempty, rational linear algebra must verify

```text
rank P=2,                       P²=μP with μ≠0,
A=(PX)|U, B=(PY)|U, C=(PZ)|U are units,
[C]=[B]⁻¹[A]⁻¹,                λ|U≠0 and Pγ≠0.
```

Failure of any condition certifies the empty branch. After they pass, choose a computable
`g₀∈PGL₂(ℚ)` carrying `[Pγ]` to `ker(λ|U)` and let `B_p` be the rational Borel stabilizing
`[Pγ]`. The sole residual question is

```text
Γ ∩ g₀B_p ≠ ∅,       Γ=⟨[A],[B]⟩.
```

The identity `P²=μP` is not a rank-only assertion. For the nonempty `F₂` branch, padded states
`PM_wγ` define an injective map from semantic values to projective rays: a spelling of
`qh⁻¹` supplies a nonzero functional whose kernel identifies exactly the states of value `h`.
The restriction of `P` fixes all these rays, hence three of them force `P|U=μI` with `μ≠0`.

Uniformly over the promised empty-or-singleton inputs, `|Γ∩g₀B_p|≤1`. Conditional on a hit,
the semantic singleton argument gives `Γ∩B_p={1}`, so that hit is unique. The singular Carvalho
shell is therefore an at-most-one Borel-coset intersection problem for a two-generated rational
subgroup; faithfulness and a free orbit are conclusions of the nonempty branch, not promises in
the empty branch.

## Sharpness and Scope

Singular rank patterns are not excluded. Take

```text
A = [[1,3],[0,1]],   B = [[1,0],[3,1]],   C = B⁻¹A⁻¹
```

and lift them to `diag(A,εₓ)`, `diag(B,εᵧ)`, `diag(C,ε_z)` with each `ε∈{0,1}`.
Whenever at least one `ε` is zero, `XYZ=diag(I₂,0)` and the reduction recovers `A,B,C`.
Thus every singular rank pattern in `{2,3}³` occurs; the theorem genuinely classifies rather
than refutes the singular branch.

The ray `[1:1]` has trivial stabilizer in `⟨A,B⟩`. In affine coordinate `t`, put
`U={|t|>1}` and `W={|t|<2/3}`. Every nonzero power of `A` sends `W` into `U`, every nonzero power
of `B` sends `U` into `W`, and their nonzero powers send `1` into `U` and `W`, respectively.
Reduced-word ping-pong therefore never returns `1`. Choosing a rational row whose kernel is one
orbit ray gives an exact singleton saturated language in every displayed rank pattern.

The collapse does not prove decidability of the remaining projective group-orbit problem. It
also does not identify inverse projective edges with positive words in the two matrices. Thus it
does not prove positive `M₃(2)`, `M₂(3)`, or `M₃(4)`.

Nor does it make the raw three-state matrices preserve one common plane or kernel. Block-lower-
triangular lifts can make the images of `XYZ`, `YZX`, and `ZXY` distinct, while dual block-upper-
triangular lifts give a common image with distinct cyclic kernels; both still recognize the exact
singleton fibre on the top quotient. The theorem says that identity interleaving discards all
zero-relevant transient geometry; it does not conjugate the original controls themselves to one
block-diagonal family.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Rank-at-most-one semantic identity loops force a saturated language to be universal or empty | promotion | Lean |
| A singular identity loop in a nontrivial three-state recognizer has rank two | promotion | Lean |
| Its image sandwiches are invertible and preserve the zero language on every word | promotion | Lean |
| The rational carrier is explicitly conjugated to `ℚ²` | promotion | Lean |
| The triangle carrier has the stated invertible-3D/invertible-2D dichotomy | promotion | Lean |
| The triangle reduction is effective by rational image-basis elimination | promotion | audited extraction with fixed inverse spellings |
| A singleton `F₂` fibre gives a faithful `PGL₂` group orbit | promotion | audited fibre argument |
| This is a positive-semigroup reduction to `M₂(3)` | rejected | the inverse composite is not a positive control |
| The projective group orbit is decidable | open | no applicable theorem is established in the corpus |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: singular three-state spelling memory as an independent Carvalho escape.
REDUCED: every singular saturated carrier to an effective invertible two-state projective carrier.
EXPANDED: the Carvalho leaf is now a joint M₃(4)/dimension-two group-orbit problem.
REMAINS: decide or universalize that group orbit, or attack the everywhere-invertible 3D branch.
```
