# Factorized Binary Cross-Ratio Audit

**Date:** 2026-08-30
**Target:** `M₉(2)` through an exact binary realization of the five-generator Neary mortality family
**Verdict:** the two natural nine-state factor geometries are impossible; same-zero and nonlinear reductions remain open

## Enemy Lock

The canonical four-state prefix transducer restricts from twelve to ten states. Its two physical
generators span `M₁₀(ℚ)`, so no further exact restriction, quotient, sandwich minimization, or
internal punctuation of that pair reaches dimension nine. This audit allows a different physical
pair: source matrices may be distributed among prefix edges, edge bases may vary by state, and
each completed codeword may acquire an independent nonzero scalar.

Write the four invertible normalized Neary role matrices as

```text
R_c, E_c, R_b, E_b
```

and write `P` for the rank-one separator. For `ρ=3^β` and
`B=3^|nearyLower β body (rule c)|`, their ordered diagonal scale pairs are

```text
R_c : (B, 3),       E_c : (3, 3),
R_b : (27, 9ρ),     E_b : (3, 9ρ).
```

The arithmetic source envelope has nonempty `body`, hence `B>27`.

## Projective Rectangle Law

Suppose four units are realized, up to independent nonzero scalars, by a factorized rectangle:

```text
αA = F X₀,     βB = F X₁,
γC = G X₀,     δD = G X₁.
```

All displayed factors are units. Cancellation gives

```text
(β/α) A⁻¹B = X₀⁻¹X₁ = (δ/γ) C⁻¹D.
```

Thus `A⁻¹B` and `C⁻¹D` must be proportional. This condition is invariant under state-fibre
basis changes and independent rescaling of every source generator.

The three partitions of the four ordinary roles fail this law. Normalizing by the first diagonal
entry, which is one in every cross-ratio, gives:

```text
(R_c,E_c) | (R_b,E_b):  (3/B, 1)  versus  (1/9, 1),
(R_c,R_b) | (E_c,E_b):  (27/B,3ρ)  versus  (1, 3ρ),
(R_c,E_b) | (E_c,R_b):  (3/B, 3ρ)  versus  (9, 3ρ).
```

Each equality contradicts `B>27`. Reversing both pairs only inverts the same failed equality.

## Four-State Prefix Trees

A complete binary prefix tree with five leaves has four proper-prefix states. Assign one leaf to
`P` and the other four to the ordinary roles. Distribute arbitrary `3×3` transition factors along
the edges, subject only to exact completed products up to nonzero scalars.

Every edge on a path to an ordinary leaf is invertible. For each proper-prefix state, concatenate
the two outgoing transition matrices in their two physical-letter target blocks. Its three rows
are independent because at least one outgoing edge lies on an ordinary path.

There are three unlabelled full-tree shapes.

1. In the comb, every internal state has a private successor block. The four three-row spaces are
   independent, so the two generators' joint image has dimension twelve.
2. In either two-cherry shape, two states have the common successor pair `(root,root)`. The other
   two states each retain a private invertible successor block and contribute six independent
   dimensions. A joint image of dimension at most nine would therefore force the two cherry row
   spaces, each of dimension three, to coincide.

Coincident cherry spaces give one unit `K` with

```text
Y₀=KX₀,     Y₁=KX₁.
```

Corresponding leaf factors have equal ranks. The unique rank-one separator cannot occupy either
cherry, since it would be paired with an invertible ordinary leaf. The four cherry leaves are
therefore exactly the four ordinary roles, and their path products satisfy the projective
rectangle law. The three concrete failures above give a contradiction.

Hence every exact factor-distributed five-leaf prefix compiler has joint image dimension at least
ten. Arbitrary invertible state gauges and independent transition scalings are included. This
strictly extends the obstruction for the canonical leaf-output transducer.

## Fixed-Width Synchronization

Pure syntax cannot align five source symbols in three binary phases. A comma-free binary code of
width three has size at most two. The constant words `000` and `111` overlap themselves and are
forbidden. The other six words form the two cyclic-shift orbits

```text
{001,010,100},     {011,110,101}.
```

A comma-free code contains at most one representative of each orbit. Any nine-state
three-phase route must therefore make weighted algebra, rather than a code-language promise,
police offsets.

## Three-Phase Cyclic Cubes

A native nine-state cyclic compiler has three three-dimensional phase fibres and six factors
`X_{p,b}`, one for each phase `p` and physical bit `b`. Its eight aligned block products are the
vertices

```text
X₀,a X₁,b X₂,c.
```

If one vertex is the rank-one separator, at least one of its three factors is singular. No
invertible ordinary-role vertex can use that factor. All four ordinary codewords must therefore
occupy the opposite four-vertex face. Every such face is a factorized rectangle, up to conjugacy
when its fixed factor occurs last, and must satisfy one of the three failed projective rectangle
laws. No exact cyclic-cube encoding of the five Neary matrices exists.

There is nevertheless an exact positional factorization of the four ordinary word pairs alone.
It evades the literal three-state singleton-decoder bound by exposing the other four cube vertices
as hybrid roles. Lean checks that these hybrids create a false terminal witness on the nonhalting
source `(β,body)=(3,bbcc)`: the six blocks

```text
001 100 100 010 101 101
```

satisfy the expanded terminal equation. Thus the most economical same-zero interpretation of the
cube also fails, independently of the separator argument.

## Disposition

| Claim | Status | Evidence |
| --- | --- | --- |
| Factorized rectangles force proportional cross-ratios | formalized | abstract matrix cancellation theorem |
| No partition of the four Neary roles has proportional cross-ratios | formalized | all three concrete scale certificates |
| Four-state prefix common-image dimension is at least ten | audited | complete full-binary-tree and row-support classification |
| A width-three binary comma-free code contains at most two words | audited | complete cyclic-orbit classification |
| No exact nine-state cyclic cube encodes the five Neary matrices | audited from formalized core | singular-face reduction plus cross-ratio theorem |
| The displayed four-role cube has a nonhalting false witness | formalized | `ThreePhaseBinaryNoGo.poison_false_positive` |

The result excludes exact factor-distributed prefix/common-image compilers and exact cyclic-cube
compilers. It does not exclude a nine-state pair with changed zero-series values, a nonfactorial
state-dependent decoder, an invariant quotient not arising from the common image, a nonlinear
reduction, or the independent consequence of `GPCP(3)`.

**Formalization:** [`MatrixMortality/NearyCrossRatioNoGo.lean`](../MatrixMortality/NearyCrossRatioNoGo.lean)
and [`MatrixMortality/ThreePhaseBinaryNoGo.lean`](../MatrixMortality/ThreePhaseBinaryNoGo.lean).
