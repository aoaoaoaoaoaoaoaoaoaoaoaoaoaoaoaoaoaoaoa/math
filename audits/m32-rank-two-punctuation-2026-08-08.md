# M₃(2) Rank-Two Punctuation Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

For two rank-two `3 × 3` generators, the checked edge compression produces a two-vertex
square of nonzero `2 × 2` edges. The open question was whether this graph constraint carried
a new hard language beyond two-generator projective incidence.

It does not. Independent reconstruction decides every edge-rank pattern except one rank-one
loop with three unit edges. Lean proves that this unique hard stratum is exactly one intrinsic
generic PI₂ instance. Consequently the whole rank-(2,2) profile is many-one equivalent to
generic PI₂, conditional only on the audited effective cyclic-orbit algorithm used to discharge
the decidable cross-edge stratum.

## Punctuation Fracture

Every edge is nonzero: if `C_ij=V_iU_j`, Sylvester’s inequality gives

```text
rank(C_ij) ≥ rank(V_i)+rank(U_j)−3 = 1.
```

Write every rank-one edge as `S_e=q_e r_e`. Splitting any path at these punctuation edges gives

```text
P₀ S₁ P₁ ⋯ S_k P_k
  = (∏ r_i P_i q_(i+1)) (P₀q₁)(r_kP_k).
```

The final outer product is nonzero because every `P_i` is a unit. Hence a path product vanishes
exactly when the unit-only bridge between some consecutive punctuation edges has zero scalar
incidence.

This makes the edge-rank census exhaustive.

1. With no rank-one edge, every path is a unit.
2. With at least two rank-one edges, the unit-edge subgraph has at most two edges. Each bridge
   language is a finite union of `P Kⁿ Q`, so mortality is finitely many order-at-most-two
   recurrence tests.
3. With one rank-one cross-edge, the only bridge has form `A₁^m B A₀^n`. Its vanishing is
   equality of two positive cyclic `PGL₂(ℚ)` orbits.
4. With one rank-one loop and three units, the graph retains a genuine free two-letter bridge.

## Cyclic-Orbit Discharge

The cross-edge equation reduces effectively to

```text
Dⁿx = Fᵐt,   m,n≥0,
```

on `ℙ¹(ℚ)`. Finite or fixed orbits are enumerated. Two parabolic orbits give a bilinear
integer equation that factors into finitely many divisor cases. After diagonalizing semisimple
maps over a compositum of quadratic fields, equality becomes

```text
a x y+b x+c y+d=0,
x=ξλⁿ,   y=ημᵐ.
```

Outside a computable finite set of places, the two affine factors in the equation have equal
valuation and a unit nonzero linear combination; both are therefore `S`-units. The effective
two-variable unit-equation theorem enumerates the non-toric solutions, after which cyclic power
membership is an effective one-dimensional unit-lattice test. Binomial torus-coset cases reduce
directly to linear Diophantine equations in `m,n`.

The mixed parabolic-semisimple case similarly yields one effective unit equation unless a
semisimple fixed point is rational. In that split boundary case the test is membership of a
rational exponential sequence in one arithmetic progression, decided by denominator growth or
eventual periodicity modulo a fixed integer.

The imported effective theorem is Evertse–Győry, Theorem 1.1 and Corollary 1.2, recorded as
[`EG13`](../references/evertse-gyory-2013-effective-unit-equations.md). This dependency is
source-audited but not reimplemented in Lean.

## Intrinsic One-Loop Throat

Let the rank-one loop be `T=q r`, the unit cross-edges be `U:0→1` and `B:1→0`, and the unit
loop at vertex one be `A`. Compatibility is the common-column law

```text
T e=U e,   B e=A e.
```

Every nonempty unit bridge from vertex zero back to itself is uniquely

```text
U W B,   W ∈ {A,BU}*.
```

Thus mortality is exactly

```text
rq=0  ∨  ∃W, (rU) W (Bq)=0.
```

The first disjunct is immediate nilpotence `T²=0`. In the other branch the intrinsic PI₂
instance has controls `A,BU`, row `rU`, and column `Bq`. Its first reverse-compiler scalar is
`rq≠0`; compatibility forces its second scalar to `1`.

Lean proves more than the scalar calculation. It transports the complete compatible edge square
by an invertible source-plane change to the existing `ReverseEdge.rawEdge`, then invokes the
checked all-path converse. The final theorem retains the empty incidence word and states the
exact disjunction above for arbitrary constrained paths.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| rank-one punctuation fracture | promotion | elementary outer-product factorization |
| no-punctuation and at-least-two-punctuation strata are decidable | promotion | finite unit graph and unary recurrence reduction |
| one cross-punctuation stratum is decidable | promotion | cyclic-orbit proof audited against effective unit-equation literature |
| compatible one-loop stratum is intrinsic generic PI₂ | formalized | coordinate transport, `β=1`, and all-path equivalence checked by Lean |
| `Mort₃^(2,2) ≡ₘ GPI₂` | audited | forward rank census plus checked reverse compiler; number-theory dependency remains imported |
| rank-(2,2) contributes a separate graph machine | rejected | every graph-only residue is decidable or the intrinsic PI₂ instance |
| arbitrary PI₂ reduces to generic PI₂ | open | still needs a guarded positive-word genericizer or singular data transport |

The subsequent positive first-exit reduction supersedes the last row at bounded truth-table
level: unrestricted PI₂ now reduces to at most two GPI₂ queries. See
[`m32-two-query-genericization-2026-08-09.md`](m32-two-query-genericization-2026-08-09.md).

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: the two-vertex graph as an independent hard core; all edge-rank patterns except one intrinsic generic incidence instance
REMAINS AT THIS RATCHET: generic PI₂ itself, and the opposite genericization seam from arbitrary PI₂; the rank-(3,2) guard and cubic bridges
SUPERSEDED: `R32-S35` later removes the opposite genericization seam at bounded truth-table level
DISTANCE: rank-(2,2) is now one known projective enemy, not a graph-constrained family of new enemies
```
