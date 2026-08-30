# Actual Carvalho Slice-Density Audit

**Date:** 2026-08-30

**Author and auditor:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `8c1e4db6ac74f56a45bb8f66dd53d962407e5c93`
**Primary source:** [Carvalho 2026](../references/carvalho-2026-free-group-pcp.md), arXiv v2
preprint

## Verdict

Every fixed-`p`-exponent slice of the correlated graph emitted by Carvalho's actual cyclic-tag
transducer is Zariski dense in `PSL₂×PSL₂` under a faithful Schottky embedding. The previous
synthetic density obstruction `G3-O19` therefore extends to the actual source by a different,
program-specific argument.

This closes the actual program-graph geometry leaf and every algebraically extendable
three-dimensional carrier which genuinely retains both group coordinates. It does not prove a
same-zero language lower bound. Spelling-sensitive, graph-only nonalgebraic, singular
nonsemantic, and infinite-state constructions remain outside the theorem.

## Actual Graph

Let `C` have positive period `m`, and use Carvalho's complete numbered-state transducer `R_C`
over

```text
B={0,1,H,p}.
```

Both binary letters advance the state by one modulo `m`; `H,p` fix the state. Let `S≤F_B` be the
loop subgroup at state zero and `ψ:S→F_B` the output homomorphism. The displayed transitions give

```text
ψ(H)=H,       ψ(p)=p,       ψ(0ᵐ)=Hᵐ.
```

With `d₀=w₀p`, Carvalho's virtual endomorphism is

```text
θ(x)=d₀ ψ(x) d₀⁻¹.
```

Let `χ:F_B→ℤ` be the exponent sum of `p`, and put `K=S∩ker χ`. Fix a faithful Schottky embedding
`ρ:F_B→SL₂(ℂ)` and project it to `PSL₂`. Such an embedding is effective: embed `F_B` in `F₂` and
compose with Carvalho's displayed purely hyperbolic free subgroup of `SL₂(ℤ)`.

## Dense Projections

The second projection of the graph of `K` contains

```text
H,       pHp⁻¹.
```

Both words lie in `K`, because their transducer paths stay at state zero and their `p`-exponents
vanish. They do not commute.

The first projection, before the fixed conjugation by `d₀`, contains

```text
ψ(H)=H,       ψ(p0ᵐp⁻¹)=pHᵐp⁻¹.
```

Here `p0ᵐp⁻¹∈K`: the `m` binary transitions return to state zero, and the two `p` exponents
cancel. These two output words also do not commute. Every nonabelian subgroup of the Schottky
free group is non-virtually-solvable, while every proper algebraic subgroup of `PSL₂(ℂ)` is finite
or virtually solvable. Both graph projections are therefore Zariski dense.

## Goursat Exclusion

Let `G` be the Zariski closure of

```text
Γ₀={([ρ(θ(x))],[ρ(x)]) : x∈K}.
```

Algebraic Goursat and simplicity of `PSL₂` leave two cases: `G=PSL₂×PSL₂`, or `G` is the graph
of an algebraic automorphism. Every algebraic automorphism of `PSL₂(ℂ)` is inner.

The transducer fixes every word in `F(H,p)`. In particular, on the nonabelian subgroup

```text
L=⟨H,pHp⁻¹⟩≤K,
```

the first graph coordinate is conjugation by `ρ(d₀)`. The projective image of `L` is dense, so an
automorphism-graph case would force that automorphism to be conjugation by `ρ(d₀)` everywhere.
It would then force `ψ(x)=x` projectively for every `x∈K`. Projective faithfulness loses no sign:
the torsion-free Schottky image does not contain `−I`.

Take `x=0ᵐ`. It belongs to `K`, but

```text
ψ(0ᵐ)=Hᵐ≠0ᵐ
```

in the free group. The automorphism-graph case is impossible. Hence `Γ₀` is dense in the full
product.

For every `t∈ℤ`, the element `pᵗ` lies in `S` and has character `t`. Therefore

```text
{x∈S : χ(x)=t}=pᵗK,
```

and its correlated graph is a translate of `Γ₀`. Every fixed-character slice is dense.

## Theorem 4.1 Maps

For the original partial transducer, every loop at the distinguished state has input
`#x#⁻¹` with `x∈S` and output

```text
# d₀ψ(x)d₀⁻¹ #⁻¹.
```

Thus the correlated graph of Carvalho's actual Theorem 4.1 homomorphisms `g,h` is obtained from
the graph of `θ,id_S` by fixed coordinatewise conjugations. These conjugations preserve density,
and the source character `κ=χ∘h` selects exactly the slices above.

## Carrier Consequence

Any rational multiplicative carrier which extends algebraically from this actual graph and acts
nontrivially through both `PSL₂` factors has dimension at least four. After passage to
`SL₂×SL₂`, an irreducible using both factors has dimension `(a+1)(b+1)≥4`; separate nontrivial
constituents cost at least `2+2`. The same restriction applies to projective carriers after
lifting and to two-dimensional affine cocycles after homogenization and complete reducibility.

Density does not transfer automatically to language Hankel rank. A smaller representation may
forget group values while preserving only the zero predicate on positive spellings. The surviving
Carvalho leaf must exploit precisely that nonalgebraic or spelling-sensitive possibility.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The kernel-character graph has dense projections | promotion | explicit noncommuting input and output pairs |
| The actual kernel-character graph is dense in `PSL₂²` | promotion | algebraic Goursat, fixed marker subgroup, `0ᵐ` contradiction |
| Every actual fixed-character slice is dense | promotion | translation by the graph of `pᵗ` |
| Every algebraic carrier using both factors needs dimension at least four | promotion | characteristic-zero product-representation classification |
| Every three-state same-zero carrier is impossible | rejected | language rank need not retain the semantic graph |
| `M₃(4)` follows | rejected | the spelling-sensitive/nonalgebraic carrier remains open |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: a proper algebraic three-dimensional quotient of the actual Carvalho program graph.
REMAINS: direct spelling-sensitive, graph-only nonalgebraic detection on the three-positive cover.
```
