# Correlated Affine-Slice Density Audit

**Date:** 2026-08-11  
**Author and auditor:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `da513368b44e96361ae25c6d4722161653c64c94` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3bf0-b850-83ea-939e-39b55003266c
**Primary source:** [Carvalho 2026](../references/carvalho-2026-free-group-pcp.md), arXiv v2
preprint

## Verdict

No `GPCP(3)`, three-state scalar-zero compiler, or `M₃(4)` theorem is obtained. The report proves
two narrower facts:

1. Carvalho's `p`-exponent character is shared by `g` and `h` on the entire source group.
2. Those coarse promises alone cannot justify algebraic dimension reduction: a synthetic
   correlated graph with the same promises has Zariski-dense fixed-character slices and forces
   every algebraic two-factor carrier to dimension at least four.

The second result is not a theorem about the graph emitted by Carvalho's cyclic-tag reduction.
The report's synthetic language even has a two-state same-zero detector. Its value is to close a
promise-only inference, not the actual graph-specific lane.

## Actual Source Character

Carvalho's transducer has alphabet `{0,1,#,H,p}` and character `χ(p)=1`, zero on every other
generator. The displayed numbered-state transitions satisfy equal input and output `χ`. The
entry edge `#|#w₀p` has output-minus-input defect one, and its inverse has defect minus one.

Every nonempty reduced closed path at the initial state enters the numbered component once and
leaves it once. Its total input and output characters are therefore equal. In Theorem 4.1, `h`
maps a free basis to the input labels of such loops and `g` maps it to their output labels. Hence

```text
χ∘g = χ∘h
```

on the whole source group. This strengthens the earlier exponent-one equalizer audit, where only
`κ=χ∘h` on accepting elements was operationally required. The conclusion is derived from the
paper's explicit construction and is not separately stated there.

## Synthetic Graph

Let `F=F(a,b)`, `h=id`, `g(a)=a`, `g(b)=b²`, and `κ=expₐ`. Free-product normal form shows

```text
Eq(g,h)=⟨a⟩,
Eq(g,h)∩κ⁻¹(t)={aᵗ}.
```

Indeed, every reduced word outside `⟨a⟩` contains a nonzero `b` syllable; `g` doubles each such
syllable without creating cancellation. Thus the example has injective `h`, a shared primitive
character, cyclic equalizer, and singleton exponent-one slice.

Under the checked three-positive cover

```text
x↦a,    y↦b,    z↦b⁻¹a⁻¹,
ω(x)=1, ω(y)=0, ω(z)=−1,
```

every arbitrary positive word satisfies `ω(w)=κ(π(w))`, and every group element has a positive
spelling of its matching weight. The accepted positive language is exactly `π(w)=a`.

## Density Proof

Use Carvalho's faithful embedding

```text
P=ρ(a)=[[3,2],[1,1]],    Q=ρ(b)=[[1,1],[2,3]].
```

The paper records that `P,Q` freely generate a subgroup of `SL₂(ℤ)` whose nonidentity elements
are hyperbolic. Put `K=ker κ`. The second projection of the correlated graph of `K` contains
`Q,PQP⁻¹`; the first contains `Q²,PQ²P⁻¹`. Each pair generates a nonabelian free subgroup, hence
is Zariski dense in `PSL₂(ℂ)` because every proper algebraic subgroup is finite or virtually
solvable.

Let `H` be the closure of the correlated graph. Algebraic Goursat and simplicity of `PSL₂` leave
the full product or the graph of an algebraic automorphism. Every algebraic automorphism of
`PSL₂(ℂ)` is inner. It cannot send the projective class of `Q` to that of `Q²`, because

```text
tr(Q)²/det(Q)=16,    tr(Q²)²/det(Q²)=196.
```

Therefore `H=PSL₂×PSL₂`. Since `κ⁻¹(t)=aᵗK`, every fixed-character graph slice is a translate of
this dense graph and remains dense.

## Algebraic Carrier Bound

A rational multiplicative carrier on the correlated graph extends across the Zariski closure.
After passage to the simply connected cover, it is a rational representation of
`SL₂×SL₂`. In characteristic zero, irreducibles are

```text
Symᵐ(ℚ²) ⊠ Symⁿ(ℚ²)
```

of dimension `(m+1)(n+1)`. A constituent on which both factors act has dimension at least four;
two separate nontrivial constituents cost at least `2+2`. Thus a carrier of dimension at most
three kills one factor. Projective representations give the same conclusion after lifting.
Homogenizing a two-dimensional affine cocycle gives a three-dimensional extension by a trivial
module; complete reducibility splits it, so the affine action is conjugate to its linear part.

This proves a dimension-four theorem only for algebraically extendable carriers which genuinely
retain both group coordinates. It does not apply to spelling-sensitive transition matrices,
nonalgebraic graph-only actions, or infinite-dimensional residues followed by scalarization.

## Hankel Certificate

For the canonical mixed action `X↦ρ(g(u))Xρ(h(u))⁻¹`, take `X₀=I₂` and read the lower-left entry.
Every nonidentity matrix in `ρ(F)` is hyperbolic, while an upper-triangular integral matrix of
determinant one has trace `±2`. The coefficient therefore vanishes exactly when `g(u)=h(u)`.

On prefixes `ε,x,y,xy` and suffixes `ε,z,xz,zy`, exact rational evaluation gives

```text
[[ 0, −2,   1, 465],
 [ 0,  1,  22,  51],
 [ 2,  0, 429,  23],
 [−1,  0, 843,   2]],
```

with determinant `1,197,990`. The audit independently reproduced all sixteen entries and the
determinant from the displayed matrices using exact SymPy arithmetic. The four-dimensional mixed
module supplies the matching upper bound for this coefficient series.

## Critical Limitation

The synthetic accepted predicate is `π(w)=a`. The report itself exhibits a two-state coefficient
whose zero set is this language. Therefore:

- rank four of the canonical mixed coefficient is not rank four of the language;
- density of a pair carrier does not exclude a nonsemantic same-zero detector;
- the example does not prove the actual Carvalho program graph dense;
- it does not close spelling-sensitive or graph-only three-state carriers.

The only lawful strategic conclusion is that the globally shared character, injective `h`,
cyclic equalizer, and singleton affine slice do not by themselves authorize an algebraic
compression.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Carvalho's actual maps share `χ` globally | audited | transition table and Theorem 4.1 construction |
| The synthetic equalizer is `⟨a⟩` | audited | free-product normal form |
| Every fixed-character synthetic graph slice is dense in `PSL₂²` | audited | dense projections, Goursat, trace-squared obstruction |
| Every algebraic carrier using both factors needs dimension at least four | audited | characteristic-zero representation classification |
| The displayed mixed coefficient has Hankel rank four | audited | irreducibility and reproduced nonzero minor |
| The actual Carvalho program graph has the same closure | rejected | not proved |
| The synthetic language needs four states up to same-zero equivalence | rejected | explicit two-state detector |
| `M₃(4)` follows | rejected | no three-control compiler or actual-source lower bound |

## Master Delta

```text
MASTER VERDICT: still open.
ADDED: χ∘g=χ∘h globally for the actual Carvalho source.
REMOVED: any dimension-three algebraic compression theorem based only on the coarse promises.
REMAINS: exploit the actual program graph, or build a spelling-sensitive/nonalgebraic carrier.
```
