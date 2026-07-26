# CHHN All-Placement Rank Audit

**Date:** 2026-07-26  
**Target:** `MM-O01`, exact minimization of the literal three-generator CHHN packing  
**Verdict:** accepted and formalized

## Claim

Place the four ordinary side-normal Neary matrices and the rank-one boundary separator into
the five slots of the two-block CHHN packing in any order. The resulting three-generator
`6 × 6` scalar series has exact linear-representation dimension six whenever `β≥3` and the
tag body is nonempty.

The claim ranges over all `5!=120` placements. It concerns exact coefficient equality. It does
not lower-bound a different rational series with the same zero set.

## Structural Reconstruction

The packing is defined over an arbitrary field by

```text
V  = [[0,G₀],[I,0]],
B₁ = [[G₁,G₂],[0,0]],
B₂ = [[G₃,G₄],[0,0]].
```

The packed row and column are `(L,0)` and `(C,0)`. Instead of expanding a `6 × 6`
determinant for every placement, the formal proof splits each packed vector into two native
three-state blocks.

Five separator positions require three independence kernels:

```text
root separator:     LI[L, LG₂, LG₄],
leading separator:  LI[L, LG₀, LG₂] and LI[LG₀, LG₂, LG₄],
trailing separator: LI[L, LG₀, L(G₁G₀)].
```

Each kernel produces six independent packed prefix rows. Two ordinary payload slots with

```text
LI[C, GᵢC, GⱼC]
```

produce six independent packed suffix columns. Their product is a nonsingular finite Hankel
section.

For the Neary family, the row conditions reduce to finite `3 × 3` determinants. Their
nonvanishing uses only:

- `β≥3`;
- the body is nonempty;
- `ternaryCode(tagCode β b)>50`;
- `ternaryCode(rule-c lower)>25`;
- the leading nonzero ternary digit gives
  `3·ternaryCode(rule-c lower)>3^length`.

The suffix proof does not need the two difficult mixed rule-column determinants. For every
placement, at least one of the semantic pairs `(R_c,D_c)` and `(R_b,D_b)` avoids the root.
Those two column determinants reduce respectively to positive multiples of

```text
3^length(rule-c lower)−3
```

and

```text
3^length(marker)−9.
```

This selection removes the modular arithmetic present in the original raw report.

## Formal Boundary

[`MatrixMortality/CHHNPacking.lean`](../MatrixMortality/CHHNPacking.lean) proves the generic
packing algebra, the three six-vector kernels, the five prefix families, the suffix family,
the finite-Hankel factorization, and the generic six-state lower bound.

[`MatrixMortality/CHHNPackingRank.lean`](../MatrixMortality/CHHNPackingRank.lean) proves the
Neary arithmetic conditions, selects a valid column pair for every placement, discharges all
five separator cases, and exports:

```text
chhnNeary_exactRepresentation_six_le_card
```

The theorem quantifies over every finite exact realization over `ℚ` and concludes that its
state-cardinality is at least six.

The declaration is included in `AxiomAudit.lean`; its transitive axiom set is checked against
the reviewed snapshot. No external theorem or computational certificate enters the proof.

## Independent Executable Check

[`tools/audit_chhn_packing_rank.py`](../tools/audit_chhn_packing_rank.py) reconstructs all 120
symbolic placements in SymPy. For every placement it verifies:

1. the selected six-prefix determinant equals the appropriate structural factor up to sign;
2. the semantic easy-pair suffix determinant equals the square of its native three-state
   determinant up to sign.

The executable check is redundant evidence. Lean owns the theorem.

## Consequence

Exact restriction, quotient, similarity, or reachable/observable minimization of any literal
placement cannot produce a five-state representation of the same scalar series. A proof of
`M₅(3)` from this neighborhood must change the nonzero coefficients, change the physical
packing, or use a non-linear/same-zero mechanism.
