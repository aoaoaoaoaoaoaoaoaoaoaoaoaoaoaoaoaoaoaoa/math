# Invertible Fibre-Span Audit

**Date:** 2026-08-30
**Author and auditor:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `31c55e8`
**Formal owner:**
[`PositiveFreeCancellation.lean`](../MatrixMortality/PositiveFreeCancellation.lean)

## Verdict

An everywhere-invertible three-state scalar carrier on the positive triangle cover has a rigid
fibre geometry. For each `q∈F₂`, let

```text
C_q = span { M_w γ : π(w)=q }.
```

Positive surjectivity and finite-dimensionality imply

```text
M_u C_q = C_{π(u)q}
```

for every positive word `u`. Thus all `C_q` have one common positive dimension. If a nonzero row
`λ` vanishes on every positive spelling of one fibre, then that fibre lies in `ker λ`; in
dimension three its dimension is therefore exactly one or two.

This converts the invertible spelling-sensitive problem into a group orbit on lines or planes.
It is not a reduction to the positive two-generator mortality problem. The reverse orbit edges
use inverses of the linear transitions, and those inverses need not be positive generators or
equal any positive spelling as operators.

## Exact Fibre Law

Let `π:S*→G` be a surjective monoid map to a group, let every letter act by a linear equivalence
`T_s` on a finite-dimensional vector space `V`, and fix `γ∈V`. Prefixing gives the immediate
inclusion

```text
T_u C_q ⊆ C_{π(u)q}.
```

Choose a positive word `v` with `π(v)=π(u)⁻¹`. Prefixing by `v` gives

```text
T_v C_{π(u)q} ⊆ C_q.
```

Both `T_u` and `T_v` preserve dimension. The two inclusions force equality of the dimensions and
then equality in the first inclusion. Lean proves this as
`positiveFibreSpan_word_map_eq`. Applying the inverse equivalence gives
`positiveFibreSpan_word_symm_map_eq`.

Surjectivity supplies a positive spelling of every `q`, so every `C_q` is an equivalence-image of
`C_1`. If `γ≠0`, no `C_q` is zero. Lean proves the common-rank and nonzero conclusions separately.

## Scalar Boundary

For any linear functional `λ`, Lean proves the exact equivalence

```text
∀w, π(w)=q → λ(M_wγ)=0    ⇔    C_q ≤ ker λ.
```

When `dim V=3`, `γ≠0`, and `λ≠0`, the left side therefore forces
`dim C_q∈{1,2}`. Lean derives `dim ker λ=2`; in the rank-two branch this identifies
`C_q=ker λ`. In the rank-one branch, acceptance is point-to-hyperplane incidence for the induced
projective group orbit.

For the triangle cover, Lean specializes the law letterwise. The matrices for `x` and `y`,
together with their linear inverses, move the fibre family exactly by left multiplication in
`F₂`. The `z` transition and the composite group action of `y⁻¹x⁻¹` land on the same fibre
subspace, although the two operators need not agree on `V`.

## Kernel-Orbit Algebra

The formalization defines

```text
A = span { M_w : π(w)=1 } ≤ End(V).
```

Concatenation of positive identity words and bilinearity prove that `A` is a unital
`K`-subalgebra. Lean then proves

```text
C_1 = Aγ.
```

For the triangle cover over an effective field, this algebra is computable. The language
`π⁻¹(1)` is an effective context-free language: the free-group word problem is context-free and
the triangle substitution is a fixed inverse homomorphism. Given a finite grammar, attach an
endomorphism subspace to every nonterminal and iterate the production equations using span,
matrix multiplication, and the terminal matrices. The simultaneous sequence is ascending; each
strict update raises the sum of the subspace dimensions, bounded by the number of nonterminals
times `(dim V)²`. A stage with no change is a fixed point. Induction on derivation height proves
that its start component is exactly `A`. The Lean file formalizes the algebra and orbit equality,
not this grammar extraction algorithm.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Prefixing maps each fibre span exactly to its group translate | promotion | Lean theorem `positiveFibreSpan_word_map_eq` |
| All fibres have one positive dimension | promotion | Lean theorems `positiveFibreSpan_finrank_eq_identity`, `positiveFibreSpan_ne_bot` |
| A vanished three-dimensional fibre has rank one or two | promotion | Lean theorem `positiveFibreSpan_finrank_one_or_two` |
| The identity fibre is the seed orbit of a unital operator algebra | promotion | Lean theorem `positiveIdentityAlgebra_map_apply_eq_fibre` |
| The triangle kernel-orbit algebra is effectively computable | promotion | finite context-free subspace saturation |
| The problem reduces to positive `M₃(2)` | rejected | inverse orbit edges are not positive controls |
| Every spelling-sensitive three-state carrier is impossible | rejected | singular transitions remain outside the theorem |
| `M₃(4)` follows | rejected | no scalar carrier or undecidability reduction is constructed |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: an unstructured everywhere-invertible infinite-fibre carrier.
REDUCED: the invertible branch to computable line/plane group-orbit incidence.
REMAINS: exploit or obstruct those group orbits, and classify singular spelling-sensitive carriers.
```
