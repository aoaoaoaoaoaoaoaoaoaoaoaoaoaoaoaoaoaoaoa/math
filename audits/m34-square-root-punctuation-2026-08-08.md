# Square-Root Punctuation Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four `3 × 3` integer matrices, `M₃(4)`

External attack: [shared Pro conversation](https://chatgpt.com/share/6a779582-1108-83ea-a8a0-f1bf42c1f9b1)

## Verdict

The report does not prove `M₃(4)`, but it discovers a live direct-mortality architecture and
closes its obvious linear completion. A rational rank-two generator `S`, computable from the
deletion width alone, squares to the normalized rank-one terminal separator. Mortality of the
resulting four matrices is therefore exactly scalar zero on the full language of words avoiding
`SS`. The remaining problem is neither punctuation placement nor arbitrary-word soundness: it is
a uniform three-state same-zero compiler on that `SS`-free subshift.

The formal fracture theorem is stronger than the report. It assumes only

```text
S² = uvᵀ
```

over an arbitrary field. It needs neither `rank S=2`, normalization `vᵀu=1`, nor a maximal-run
decomposition. Recursive cutting at any occurrence of `SS` suffices.

## Checked Fracture

For ordinary matrices `X_a`, define `H_none=S`, `H_(some a)=X_a` and

```text
c(w)=vᵀH_wu.
```

Whenever `w=l SS r`, outer-product multiplication gives

```text
c(w)=c(l)c(r).
```

Strong induction on word length therefore proves that every scalar-zero word has an `SS`-free
scalar-zero residual. A zero matrix word is automatically scalar-zero. Conversely, if an
`SS`-free word `z` has `c(z)=0`, then

```text
SS z SS = (uvᵀ)H_z(uvᵀ)=0.
```

Lean proves the exact arbitrary-word equivalence as

```text
IsMortal({X_a}∪{S})
  ↔ ∃ z, z avoids SS ∧ vᵀH_zu=0.
```

Exterior punctuation, adjacent runs, singular ordinary controls, zero control-only products,
and malformed isolated occurrences of `S` are all included. Nothing is relegated to an intended
grammar.

## Explicit Neary Root

In side-normal coordinates put

```text
λ=(1,0,0),
γ=(μ,−1,T)ᵀ,
μ=[10^β]₃,
T=3^(β+1),
u=γ/μ.
```

The report's matrix is

```text
S=[[1,       0, 0],
   [−1/μ,    0, 0],
   [T/μ+1,   μ, 0]].
```

Lean checks

```text
S²=uλ,
rank S=2,
det S=0.
```

The rank proof supplies explicit `3×2` and `2×3` factors together with a left and right inverse,
not a numerical determinant heuristic. The formula depends on `β` but not on the source body.

Assign the isolated physical letter `S` to the role `R_b`. Every legal width-`β` history consists
of one rule followed by `β−1` erasures, so for the master regime `β≥3` it lies in the `SS`-free
subshift. A complete reduction would follow from matrices for the other three roles satisfying

```text
λH_z(γ/μ)=0  ↔  λA_{π(z)}γ=0
```

for every `SS`-free physical word `z`. Only the zero sets must agree.

## Exact-Series Rigidity

The report correctly observes that preserving the old coefficient values cannot produce the
required singular `R_b` matrix. The formal proof contracts the certificate further. Take the
three prefixes and suffixes

```text
ε, D_c, D_b.
```

Every one of the nine sandwiches `p R_b q` is `R_bR_b`-free. Their native reachable and
observable factors are

```text
R=[[1,0,0],                  C=[γ, A_Dc γ, A_Db γ],
   [1,1,2],
   [1,1,u_b]],
```

with

```text
det R=u_b−2,
det C=T²(T−1),
det A_Rb=81T.
```

All are nonzero for `β≥3`. Hence the inserted coefficient section

```text
R A_Rb C
```

is invertible. Any three-state representation agreeing on those nine words has inserted section
`R′ H_Rb C′`; its invertibility forces `H_Rb` itself to be invertible. Lean proves the same
conclusion when every target coefficient is multiplied by an arbitrary nonzero product of
letter weights. Thus similarity, exact quotient or restriction, rational gauge, and per-letter
rescaling cannot complete the square-root architecture.

## Additive-Fusion Obstruction

The report also analyzes the direct additive family

```text
S=αA+cA^ε(γλ)A^δ,     α≠0, ε,δ∈{0,1}.
```

Its source-specific input is the reverse-marker exclusion

```text
λA_w⁻¹γ ≠ 0
```

for every active word. In side-normal word coordinates, equality would force `U(w)=hV(w)`;
the upper word ends in `1`, while the lower word and hence `hV(w)` end in `0`. The empty word
gives `λγ=μ≠0`.

The matrix determinant lemma leaves one possible singular coefficient. At that value, the fused
matrix has rank two, with a one-dimensional kernel and two-dimensional image. Reverse-marker
exclusion makes every intervening action injective on that image. Consequently every physical
word containing the fused generator has rank exactly two; words without it are products of
units. The entire additive family is immortal.

This argument is accepted as an exact paper proof but is not transcribed into Lean. It closes a
failed local ansatz rather than supplying the positive mechanism, so its formalization is not on
the present hot path. The simpler protected-upper-plane obstruction has the same disposition.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `S²=uvᵀ` gives the exact `SS`-free mortality grammar | promotion | Lean theorem `SquareRootPunctuation.isMortal_iff_exists_squareFree_zero` |
| The displayed Neary matrix is a rational rank-two square root | promotion | Lean theorems `nearySquareRoot_sq`, `nearySquareRoot_rank` |
| Exact coefficient preservation on the `SS`-free subshift forces `H_Rb` invertible | promotion | Lean theorem `ruleB_isUnit_of_exact_on_squareFree` |
| Nonzero per-letter weighting evades the rigidity | rejected | Lean theorem `ruleB_isUnit_of_weighted_exact_on_squareFree` |
| Every boundary-aligned additive fusion is immortal | audited, not formalized | reverse-marker and kernel-image proof |
| The `SS`-free same-zero compiler exists | open | no matrices supplied |
| `M₃(4)` follows | rejected | conditional on the preceding open compiler |

## Master Delta

```text
MASTER VERDICT: still open.
ADDED: a uniform rank-two square root of punctuation; a complete all-word mortality grammar;
       an exact and weighted-series rigidity theorem.
REMOVED: punctuation placement as an outstanding obligation; all boundary-aligned additive
         fusions; similarity, exact values, and per-letter scaling as completions.
REMAINS: a genuinely zero-set nonlinear three-state compiler on the SS-free subshift.
DISTANCE: one sharply stated same-zero theorem. A solution closes M₃(4) directly.
```

## Artifact

[`SquareRootPunctuation.lean`](MatrixMortality/SquareRootPunctuation.lean)
