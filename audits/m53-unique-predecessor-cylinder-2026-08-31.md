# Unique Predecessor Cylinder Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** a nonterminal full-erasure-tail pole confines its primitive predecessor to one
explicit high-precision three-adic cylinder

[`MM-S63`](../SALVAGE.md#mm-s63-full-tail-last-step-resonance) fixes the last common
normalization depth but does not use its value in the target congruence. This audit substitutes
that resonance into the exact raw carrier gap and records the resulting predecessor cylinder.

## Exact Cylinder

Let primitive `(n,d)` cross a physical role block `z`. Put

```text
a=upperLength(z),      E=P_zd−V_zn.
```

Write its unreduced successor as `s(n',d')`, where `s≠0` and `(n',d')` is primitive. A
nonterminal pole against a target ending in `β` erasure tiles gives

```text
3^β ∣ d'−n'.                                            (1)
```

The last-step resonance is

```text
g=v₃(s)=a−1.                                            (2)
```

Thus `3^(g+β)` divides the left side of the raw gap equation

```text
s(d'−n')=μ(H·3^a d−3E).                                (3)
```

The marker `μ=2·3^β−1` is coprime to three. Cancelling it from (3), substituting (2), and
cancelling the explicit factor three gives

```text
3^(a+β−2) ∣ E−3^(a−1)Hd.                               (4)
```

This is a single predecessor residue class modulo `3^(a+β−2)`, not merely a valuation shell.
Lean proves both the raw divisibility theorem and an adapter deriving it directly from the
physical target pole.

## Literal Deletion

For `z=D_c`, the physical codes are

```text
a=1,      P_z=H,      V_z=2.
```

Equation (4) becomes `3^(β−1)∣−2n`. Coprimality with two yields

```text
3^(β−1) ∣ n.                                            (5)
```

This consequence is sharp. The explicit primitive carrier after the first distinguished
`D_c` has

```text
n=(2h+1)(15h+7),      2h+1=3^(β−1),
```

so it already satisfies (5). The cylinder therefore cannot be discarded as arithmetically
empty.

## Master Boundary

The first theorem above this result that would establish swapped-setter avoidance is global:
from either setter reset, every finite physical role-block history whose live state hits the
next physical pole must have equal target codes `P=V`. That equality invokes the checked Neary
decoder and gives a genuine tag-system halt.

The present suffix interface does not discharge that theorem. `HasErasureTail β target` means
`β` consecutive erasure tiles; an arbitrary physical role block is known only to end in one
erasure tile. Even within the full-tail subbranch, (4) selects a predecessor cylinder but does
not exclude it. A complete proof must either force the long tail at an earliest false pole or
transport an analogous ancestry invariant through arbitrary physical target suffixes. The
matrix-level `MM-S01`/`MM-M04` bridge from setter avoidance to `M₅(3)` also remains audited rather
than Lean-formalized.

## Verification

[`SwappedSetterPredecessorCylinder.lean`](../MatrixMortality/SwappedSetterPredecessorCylinder.lean)
contains the exact cylinder, physical pole adapter, literal-`D_c` consequence, and sharpness
witness. The module builds warning-free; its namespace passes the default environment linters,
and all publication-facing declarations are listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterPredecessorCylinder.lean`](../MatrixMortality/SwappedSetterPredecessorCylinder.lean)
- [`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry)
- [`MM-S63`](../SALVAGE.md#mm-s63-full-tail-last-step-resonance)
- [`MM-S64`](../SALVAGE.md#mm-s64-unique-predecessor-cylinder)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
