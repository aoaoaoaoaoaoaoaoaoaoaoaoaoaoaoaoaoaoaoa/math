# Live Three-Block Charge Frontier Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every nonhalting full-tail pole behind `w;D_c;D_c` carries one exact nonzero charge
from the predecessor cylinder to the literal target suffix carry, and all three preceding product
boundaries are automatically live

## Interface

Let a primitive origin carrier `(m₋₁,e₋₁)` cross a physical role block `w` to primitive
`(n₀,d₀)`, then cross two separate singleton `D_c` blocks to primitive `(n₁,d₁)` and
`(n₂,d₂)`. All three raw normalization equations and nonzero scales are explicit. Assume only
that the last state is live and meets a nonterminal target pole whose spelling ends in `β`
erasure tiles.

The theorem does not concatenate the two singleton transfers. Each retains its own square-run
boundary and normalization scale.

## Charge Chain

Write `ρ=3^β`, `μ=2ρ−1`, `H=5ρ−1`, and let `g` be the initial scale depth. In the nonhalting
branch, Lean constructs three scale units and four nonzero charges such that

```text
d₀−n₀=ρq₀,
P_we₋₁−V_wm₋₁−3^gHe₋₁=3^(g+β−1)k₀,
n₁=3^(β−1)k₁,
d₂−n₂=ρq₂,
s₀=3^g u₀,      s₁=3u₁,      s₂=u₂,
```

with `3∤uᵢ` for each `i`, and proves

```text
μk₀=−u₀q₀,
u₁k₁=H(2q₀−d₀),
u₂q₂=2μk₁.                                             (1)
```

If `U` and `L` are the upper and lower prefixes left after the target's matched erasure tail,
then `q₂=d₂(U+1)−n₂(L+1)`. The exact balanced suffix carry after the matched `β` false digits is
`(ρ−1)q₂`; it is stored in the witness rather than inferred from divisibility alone.
Eliminating `q₀` and `k₁` gives the direct braid

```text
u₀u₁u₂·((ρ−1)q₂)=−2μH(ρ−1)·(2μk₀+u₀d₀).             (2)
```

The left side contains the literal target suffix carry; the right side contains only the
initial predecessor-cylinder quotient, its normalization unit, and the antecedent denominator.

## Earliestness

No local live-prefix hypothesis is added. The initial deep cylinder excludes `e₋₁=0`; primitive
full-gap congruence excludes `d₀=0`; and the deep middle numerator excludes `d₁=0`. Exact
represented-denominator transport then pulls the assumed final live boundary backward through
the second `D_c`, the first `D_c`, and `w`. The theorem returns the resulting
`LiveThreeBlockPrefix` certificate.

Thus local earliestness does not kill (2). A remaining earliest-pole argument must constrain the
history before `w` or the Neary prefix ancestry encoded by `q₂`.

## Boundary

The result requires `β≥2`, a compiler body of length at least `β−1`, a full `β`-erasure target
tail, primitive carriers, and explicit nonzero integral normalizations. It neither forces an
arbitrary physical target to have that tail nor proves the nonzero charge chain impossible. No
`M₅(3)` conclusion follows.

## Verification

[`SwappedSetterCylinderCharge.lean`](../MatrixMortality/SwappedSetterCylinderCharge.lean)
contains the exact factorization, carry, denominator-transport, local-live, and three-block
composition theorems. The module builds warning-free; its namespace passes all default linters;
LSP reports no diagnostics; and every public theorem is listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterCylinderCharge.lean`](../MatrixMortality/SwappedSetterCylinderCharge.lean)
- [`MM-S71`](../SALVAGE.md#mm-s71-three-block-backward-frontier)
- [`MM-O27`](../SALVAGE.md#mm-o27-reachable-predecessor-cylinder)
- [`MM-S73`](../SALVAGE.md#mm-s73-live-three-block-charge-frontier)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
