# M₅(3) post-RcDb chamber audit

## Boundary

This audit concerns the next physical block after one literal local history:

```text
empty-front seed → (R_c,D_b) backward pullback → singleton D_c pullback.
```

It proves that every subsequent physical block misses the `MM-S104` slope chamber. It does not
prove that `(R_c,D_b)` is forced by a chamber entry, that the local ray is reachable from the
encoded entry, or that any local target is a pole.

## Canonical intercept

Put

```text
ρ=3^β,  r=ρ−2,  H=5ρ−1,  μ=2ρ−1,  Q=3^(β−6).
```

Every width-`β` physical empty-front seed `c`, with `β≥6`, satisfies `c>8ρ²`. For the canonical
body `b c^(β−2)` and literal block `(R_c,D_b)`, define

```text
T=H+rc,
G=(ρ−9)T−54ρHμ,
V₂=90ρ²−9ρ+7.
```

After pulling the near-diagonal image through singleton `D_c`, its boundary intercept is

```text
Ξ = μr²G / ((r²+2r)G+6μV₂T).
```

Lean proves `T>0`, `G>0`, and positivity of every displayed denominator. Polynomial certificates
then give

```text
6Q/5 < Ξ,
β=6  →  Ξ < 2−H/(9ρ−1),
β≥7  →  Ξ < 14Q/9−H/(9ρ−1).
```

No numerical sampling enters these inequalities.

## Affine automaton

For a subsequent physical block with lower code `V`, the backward slope is `X/V`, where its
upper numerator is generated exactly by

```text
b : X ↦ 9ρX+H,
c : X ↦ 3X−r.
```

This follows by substituting `Ξ=μry/(H+ry)` into the exact inverse-block formula; it is not an
approximation to the projective action.

A first `c` update sends `Ξ` below `−1`. Both updates preserve that negative cone, so every
`c`-leading next block has negative slope.

For a `b`-leading block, two affine margins are invariant. The lower potential starts at zero
after the first `b` and implies

```text
X > (Ξ+1/2)A,
```

where `A` is the upper spelling power. The fixed-point margin `H/(9ρ−1)` preserves the relevant
upper bound from the canonical intercept.

## Physical partition

Let `m` be the lower spelling length and `L` the upper spelling length. Exact ternary bounds give

| Case | Lower code `V` |
|---|---|
| `m≤L+β−6` | `V<QA` |
| `m≥L+β−4` | `3QA≤V` |
| `m=L+β−5`, first tile `D_b` | `2QA≤V` |
| `m=L+β−5`, first tile `R_b` | `14QA≤9V` and `3V<5QA` |

The critical bounds use the literal swapped prefixes `2` and `112`. Combining this partition
with the affine margins yields

```text
β=6  →  slope<1 or 51/50<slope,
β≥7  →  slope<1 or 6/5<slope.
```

Since `r/(r−3)<51/50` at width six and `r/(r−3)<6/5` uniformly thereafter, no next physical
block lies in `(1,r/(r−3))`.

## Scope seam

The theorem is deliberately conditional. Canonical exact-block forcing is false at width six:
target `c^6`, body `bcbcc`, and block `(R_c,D_b,D_b)` form a lawful local contraction survivor
in the full `3H` channel. Equal-spelling `(R_c,D_b^k)` survivors and longer modular-return
survivors also occur. Their post-`D_c` intercepts need not satisfy the canonical lower bound, so
the present classification cannot be silently generalized to them.

## Verification

Formal source:
[`MatrixMortality/SwappedSetterPostRcDbAutomaton.lean`](../MatrixMortality/SwappedSetterPostRcDbAutomaton.lean)
and
[`MatrixMortality/SwappedSetterPostRcDbChamber.lean`](../MatrixMortality/SwappedSetterPostRcDbChamber.lean).

The source compiles without warnings. The namespace passes the default linters; every public
theorem is listed in `AxiomAudit.lean`; the reviewed axiom snapshot contains only standard
axioms; and the aperture scan is empty. `SwappedSetterEmptyFrontChamber.lean` now canonically
owns the empty-front seed cores and physical lower-word API reused here.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.
