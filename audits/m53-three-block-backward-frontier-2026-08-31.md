# Three-Block Backward Frontier Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** a nonterminal full-tail pole after two singleton `D_c` transfers either halts or
places the physical block before them in one exact nonzero predecessor cylinder

## Interface

Take a primitive carrier `(m,e)`. A physical role block `w` produces the raw carrier `s(n,d)`,
where `(n,d)` is primitive and `s≠0`. Two further singleton `D_c` blocks, each separated by its
own square-run boundary, produce two more explicitly normalized primitive carriers. Assume the
last carrier meets a live nonterminal target pole whose spelling ends in `β` erasure tiles.

This statement retains all three integral normalization equations. In particular, it does not
concatenate the singleton blocks into `[D_c,D_c]` or identify a later carrier with a raw-head
state.

## Composition

The `MM-S69` consuming theorem gives either `TagHaltsFrom` or

```text
d−n≠0,      3^β ∣ d−n.                                  (1)
```

In the nonhalting branch, `MM-S64` applies directly to the transition through `w`. Write

```text
g=v₃(s),      a=upperLength(w),
E=P_we−V_wm,      H=5·3^β−1.
```

Lean proves

```text
a=g+1,
3^(g+β−1) ∣ E−3^gHe.                                  (2)
```

The target-coupled nonzero gap is essential. Without it, the last-step valuation equality need
not hold; `MM-S69` supplies both nonzeroness and the full marker modulus before `MM-S64` is
invoked.

## Boundary

Equation (2) selects a cylinder to precision `a+β−2`; it does not prove that cylinder empty.
Its intended consumer is the first physical role block not equal to singleton `D_c` when the
literal-deletion numerator/gap toggle is traversed backward. The proof also retains the
full-`β`-erasure target-tail assumption. A generic physical role block guarantees only one final
erasure tile, so no global earliest-pole or `M₅(3)` theorem follows.

## Verification

[`SwappedSetterThreeBlockFrontier.lean`](../MatrixMortality/SwappedSetterThreeBlockFrontier.lean)
contains the exact composition. The module builds warning-free; its namespace passes all
default linters; LSP reports no diagnostics; and the public theorem is listed in
`AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterThreeBlockFrontier.lean`](../MatrixMortality/SwappedSetterThreeBlockFrontier.lean)
- [`MM-S64`](../SALVAGE.md#mm-s64-unique-predecessor-cylinder)
- [`MM-S69`](../SALVAGE.md#mm-s69-sequential-double-deletion-zero-gap-extinction)
- [`MM-S71`](../SALVAGE.md#mm-s71-three-block-backward-frontier)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
