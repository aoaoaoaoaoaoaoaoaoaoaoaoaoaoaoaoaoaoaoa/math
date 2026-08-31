# M₃(4) Transverse Terminal-Row Obstruction Audit

**Date:** 2026-08-30
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `5fbfc7e` on `wave3-m34-transverse`

## Verdict

No source-dependent terminal row can extend the `G3-O18` transverse-history orbit from its
singleton terminal codes to all admissible Neary bodies. The obstruction already occurs for the
admissible width-three body `bcbc`: two distinct terminal histories force any exact row to be
zero, while a checked near-fork control is nonterminal.

This kills terminal-row retuning on the fixed transverse generator and column. It does not rule
out a different transverse construction whose orbit is genuinely two-dimensional.

## Fixed Orbit

For decoded history code `κ` and phase sign `ε∈{1,−1}`, the fixed controls maintain

```text
P(κ,ε)=(8κ−ε,4κ−ε,1)ᵀ.
```

Let `r=(a,b,c)` be an arbitrary rational terminal row. Exactness on the complete raw control
monoid requires both phase spellings of every terminal history to vanish. For one terminal code
`κ`, the two equations are

```text
a(8κ−1)+b(4κ−1)+c=0,
a(8κ+1)+b(4κ+1)+c=0.
```

Their difference gives `a+b=0`; either equation then gives `4κa+c=0`. Two distinct terminal
codes `κ₁≠κ₂` force `a=0`, hence `b=c=0`.

## Concrete Fracture

`BranchingHistory.bcbcTerminalFork [false]` and
`BranchingHistory.bcbcTerminalFork [true]` are distinct terminal role words. Injectivity of the
mixed-radix code makes their codes distinct. Surjectivity of `decodePairedWord`, followed by a
leading toggle, supplies both phase spellings of each word. Therefore any row same-zero with the
paired coefficient on every raw control word is zero.

The explicit `BranchingHistory.bcbcNearForkControl` is not a paired zero. A zero terminal row
annihilates it, contradicting same-zero exactness. Lean proves the resulting statements as

```text
TransverseHistory.no_bcbc_terminal_row_section
TransverseHistory.no_sourceUniform_terminal_row_section
```

The second theorem quantifies over every set-theoretic family
`Nat → List TagLetter → Fin 3 → ℚ` and requires exactness only on admissible bodies; it therefore
excludes every computable source-dependent row family without a separate computability hypothesis.

## Scope

The proof fixes the `G3-O18` controls and initial column. A constructor may still change the
orbit, couple terminal information into the controls or column, or maintain a genuinely
two-dimensional invariant surface. The theorem does not exclude transverse rank-two geometry
itself, which `G3-O18` already realizes.

```text
MASTER VERDICT: M₃(4) remains open.
REMOVED: every singleton-row or source-dependent-row extension of the fixed G3-O18 orbit.
SURVIVOR: different transverse dynamics with a genuinely two-dimensional terminal surface,
          or one of the independent common-kernel, projective-obstruction, GPCP, or group-orbit
          lanes.
CROSS-POLLINATION: any construction useful to the nine-state binary factor route must alter the
                   singular history dynamics; terminal-row retuning cannot supply its missing
                   same-zero compression.
```

## Artifact

- [`TransverseHistory.lean`](../MatrixMortality/TransverseHistory.lean)
