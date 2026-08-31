# M₃(4) Distinct-Data Infinite-Carrier Candidate Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `e7fd3fc` on `wave3-m34-transverse`
**Formal owner:**
[`TransverseSeparatedAtlas.lean`](../MatrixMortality/TransverseSeparatedAtlas.lean)

## Verdict

One explicit source-uniform perturbation escapes the letter-blind collision of `G3-O34` while
retaining all positive prefix geometry from `G3-O30`–`G3-O33`. Both data controls have rank two,
the original nonprojective infinite carrier and arbitrary delayed terminal section survive, and
the certified `bcbc` terminal control is separated from its near-fork at every rational source.

This is a candidate mechanism, not a same-zero compiler. The complete distinct-data word dynamics
and arbitrary-word converse remain open.

## Distinct Rank-Two Data

Retain

```text
T = diag(1,2,3),              D_b(s)=D_s,
```

and define

```text
P = [[2,−1,−1],                 D_c(s)=P D_s.
     [0, 0, 1],
     [2, 1,−1]]
```

Lean computes `det(P)=−4`, proves that `P` is a unit, and transfers the exact rank-two theorem
from `D_s` through left multiplication. Both `D_b(s)` and `D_c(s)` therefore have rank two for
every `s∈ℚ`.

The maps are uniformly distinct. Their difference has `(1,0)` entry equal to one, so no source
specialization can restore letter blindness.

## Preserved Carrier And Section

The original carrier words contain only the first data letter:

```text
w_n = tⁿb.
```

Because `T` and `D_b` are unchanged, Lean proves at the actual multiplication order

```text
wordProduct(X_s,w_n) = TⁿD_s.
```

All inherited consequences apply to the right-hand side: rank is exactly two and the carrier
planes are injectively distinct with `n`. The `G3-O33` row and column section is also unchanged on
these words. For arbitrary source functions `s(σ)` and target-depth functions `N(σ)`, Lean proves

```text
linearCoefficient(X_{s(σ)}, w_n)=0  ⇔  n=N(σ)
```

under the displayed section.

## Uniform Fork Separation

Let `U_s` be the product of the certified `bcbc` terminal control and `V_s` the product of its
certified nonterminal near-fork. Direct symbolic multiplication inside Lean gives

```text
(U_s−V_s)₁₀ = 6(2s²−5s+4).
```

The quadratic has no rational or real zero. Lean proves positivity from

```text
8(2s²−5s+4) = (4s−5)²+7 > 0.
```

Consequently `U_s≠V_s` for every `s∈ℚ`. This removes the exact collision that killed the
letter-blind generator, without a source case split or terminal-row choice.

## Boundary Of The Advance

Matrix-product inequality is necessary but not sufficient for scalar separation by the eventual
terminal row and column. More importantly, two products out of the free control monoid do not
determine its complete zero language. The formalization does not prove any of the following:

1. that one terminal row vanishes on every valid paired terminal history;
2. that the same row is nonzero on the displayed near-fork;
3. that all nonterminal or malformed raw words are rejected;
4. that other terminal/nonterminal product collisions do not exist;
5. that the delayed-prefix target corresponds to the required history of an unrestricted body;
6. that `M₃(4)` is decidable or undecidable.

The correct next object is this concrete three-generator monoid. A positive attack must derive its
full state recurrence and terminal scalar. A negative attack must exhibit a new collision or a
uniform obstruction that survives the distinct data maps.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The separator is invertible with determinant `−4` | promotion | Lean theorems `separator_det`, `separator_isUnit` |
| Both distinct data maps have rank exactly two | promotion | Lean theorem `separatedData_rank_eq_two` |
| The data maps differ at every source | promotion | Lean theorem `separatedData_ne` |
| The original `tⁿb` carrier matrices survive exactly | promotion | Lean theorem `wordProduct_carrierWord` |
| Every source-indexed delayed singleton survives on those prefixes | promotion | Lean theorem `sourceFamily_delayed_carrierWord_zero_iff` |
| The terminal/near-fork product difference has the displayed positive entry | promotion | Lean theorems `bcbc_product_difference_entry`, `separation_polynomial_pos` |
| The exact `G3-O34` products are distinct at every source | promotion | Lean theorem `bcbcTerminal_wordProduct_ne_nearFork` |
| The eventual terminal scalar separates those products | open | product inequality alone does not choose a row and column |
| The candidate has the complete paired zero language | rejected | no all-word state formula or converse is proved |
| `M₃(4)` follows | rejected | the master same-zero obligation remains open |

## Formal Validation

The formal owner compiles warning-free under the repository toolchain. Publication-facing
declarations are listed in [`AxiomAudit.lean`](../AxiomAudit.lean), and their selected transitive
axiom outputs contain only the reviewed standard axioms. No `sorry`, `admit`, project axiom,
unsafe declaration, suppression, or proof aperture is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
ESCAPE: distinct rank-two data maps simultaneously preserve the infinite carrier and repair the
        first certified terminal/nonterminal product collision.
EXACT: the separating entry is 6(2s²−5s+4)>0 for every rational source.
SURVIVOR: derive the complete state recurrence and arbitrary-word zero converse, or find a new
          collision in this concrete distinct-data monoid.
```
