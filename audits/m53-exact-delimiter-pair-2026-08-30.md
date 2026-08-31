# Exact Delimiter-Pair Obstruction

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** an exact ignored-delimiter-pair semantics forces immortality; pure and fixed-context
cubic projections cannot realize the off-diagonal companion

Nothing below proves `M₅(3)` decidable or undecidable.

## Bordered Pair Closure

Let `K` be a field, let `Gᵢ,T∈M_d(K)`, and choose `e≠0` such that

```text
T²=I,        Te=e,        Gᵢe=e,        ⋂ᵢ ker Gᵢ={0}.
```

Lift the data by zero and border the toggle:

```text
Ĝᵢ=diag(Gᵢ,0),        S=[[T,a],[bᵀ,c]].
```

Suppose every double delimiter is contextually indistinguishable from two toggles:

```text
Ĝᵢ S² Ĝⱼ = Ĝᵢ Ĝⱼ                           (1)
```

for all `i,j`. Since `(S²)₁₁=I+abᵀ`, equation (1) gives

```text
(Gᵢa)(bᵀGⱼ)=0                              (2)
```

for every pair. If every `Gᵢa` vanishes, triviality of the common kernel gives `a=0`. Every
physical product then sends `(e,0)` to a vector whose first `d` coordinates still equal `e`.
Otherwise some `Gᵢa` is nonzero, and cancellation in the rank-one matrix (2) gives
`bᵀGⱼ=0` for every `j`. Hence `bᵀe=bᵀGⱼe=0`, so `(e,0)` is fixed by `S` and by every `Ĝᵢ`.
The bordered family is immortal in both cases.

The paired Neary data satisfy the hypotheses when the body is nonempty. Their common image is

```text
H=span(e_a,e_u,e_D),
```

and their common kernel is zero. The latter follows directly from the lower rows: the `b` rule
scale is `27`, both erasure scales are `3`, and the `c` rule scale is strictly greater than
`27`. A vector killed by both data matrices therefore has zero private coordinates; the upper
scale and affine rows kill the other two coordinates.

Thus a terminal-normal-form compiler cannot declare every `S²` run to be an ignored parity
pair inside the standard bordered paired lift. Square runs must carry genuine semantics. This
explains why the setter reduces the converse to a nontrivial projective transfer rather than to
the existing paired decoder.

The generic closure is Lean-checked as `exactDelimiterPair_immortal` in
[`TwoStateObstructions.lean`](../MatrixMortality/TwoStateObstructions.lean). The short concrete
paired common-kernel calculation remains an audited specialization.

## Cubic Companion Closure

The bordered toggle `MM-M02` has `S³=Π_F`, where `Π_F` is an idempotent rank-two projection.
It cannot itself be the normalized off-diagonal companion separator `E=UV` from `MM-M01`:

```text
VU=J(1),        E³=E,        E²≠E.
```

A fixed-context repair also fails for the full paired series. Suppose

```text
E=Π_F C Π_F,        Π_F=UV,        VU=I,        K=VCU.
```

Exact companion behavior forces `K` to be conjugate to `J(1)`. In a basis with `K=J(1)`, the
bridge identity for the paired series `g` becomes

```text
VB_wU = J(g(w)/α) K⁻¹ = diag(g(w)/α,1).            (3)
```

The block-Hankel rank of the right side is `rank(g)+1`: after separating its two matrix
coordinates, its block Hankel matrix is the direct sum of the Hankel matrix of `g` and the
rank-one constant series. `MM-O04` gives `rank(g)=4`, whereas the left side of (3) factors
through the four-dimensional paired carrier and therefore has block-Hankel rank at most four.
This contradiction excludes pure cubic punctuation and every fixed cubic context realizing
`MM-M01` for the full paired series.

## Former Surviving Leaf

This audit originally conjectured that absorbing the forced initial `R_c` lowered the paired
tail derivative to rank at most three. That conjecture was false.
[`MM-O18`](../SALVAGE.md#mm-o18-forced-rule-companion-toggle-wall) exhibits a nonsingular
`4×4` Hankel section on isolated-toggle words, then adjoins the compulsory constant channel to
force any exact five-state companion toggle to be invertible. Its cube therefore cannot have
rank two. The proof permits arbitrary fifth-coordinate data couplings and closes the exact
bordered-companion leaf before a square/cube fracture grammar enters.

Setter/projective, same-zero, existence-only, and scheduled source compilers remain outside both
obstructions.
