# Multiplicative Threshold Carry Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every later swapped-ternary pole has an exact finite-state multiplicative suffix
carry; a full erasure tail is terminal below the marker-scale carrier gap

[`MM-S57`](../SALVAGE.md#mm-s57-centered-history-defect-transport) shows that a general centered
history cannot be reinterpreted as a fresh raw Neary head. Its normalized defect nevertheless
retains a projective numerator and denominator. This audit derives the exact suffix invariant
carried by those two integers and identifies the condition under which it excludes a false pole.

## Threshold Product

Let `δ=D/y` be the normalized ordinary-reset defect. Choose integers `n,d` representing

```text
(H/R)δ=n/d.                                             (1)
```

For a physical target, let `P` be its swapped upper code and `V` its swapped lower code.
Substitution into the exact pole equation of `MM-S57` gives

```text
dP=nV.                                                  (2)
```

This is a multiplicative identity. It does not assert that `d−n` is a raw upper/lower word-code
difference, and therefore does not depend on the invalid sliding-window reduction rejected by
`MM-S57`.

## Exact Carry

Write the swapped ternary value of a bit as `digit(bit)∈{1,2}` and read equal-length suffixes
from least to most significant digit. Define

```text
cᵢ+d·digit(pᵢ)−n·digit(vᵢ)=3cᵢ₊₁.                     (3)
```

Lean proves both directions between a carry run and its accumulated product equation. When (2)
is factored into aligned prefixes and suffixes, the initial carry is zero and the outgoing carry
is exactly

```text
n·code(lower prefix)−d·code(upper prefix).              (4)
```

The interval

```text
|c|≤|n|+|d|                                             (5)
```

is forward invariant under (3). Thus a fixed carrier induces an exact finite automaton whose
size is independent of suffix length. It is not a uniform finite quotient across histories:
the bound grows with the carrier coefficients.

The two lower-language blocks have exact reversed actions. One erasure digit gives

```text
c+2(d−n)=3c'.                                           (6)
```

A three-digit rule block, reversed to `011`, gives

```text
c+26d−14n=27c'.                                         (7)
```

Equations (6)-(7) retain the complete integer carry; no residue truncation is used.

## Consuming Cut

Suppose the target ends in `β` erasure tiles. Its punctuated upper word and lower spelling then
have the common suffix `0^β`, whose swapped code is `3^β−1`. Applying the suffix carry to (2)
gives

```text
3^β ∣ d−n.                                              (8)
```

If additionally

```text
|d−n|<3^β,                                              (9)
```

then (8) forces `d=n`. For `d≠0`, equation (2) cancels to `P=V`. Under the compiler length
envelope, the checked Neary decoder converts this physical code equality to `TagHaltsFrom`.
Therefore a nonterminal pole with a full erasure tail must have `|d−n|≥3^β`.

## Boundary

The formal theorem accepts any integer representative `(n,d)` satisfying (1); coprimality is not
needed. It does not prove (9), does not bound carrier height uniformly across arbitrary centered
histories, and does not classify targets without a full `β`-erasure tail. The next obstruction is
the primitive carrier gap: derive (9), or another inequality that consumes (8), from the exact
centered-history recurrence. No `M₅(3)` conclusion follows from this audit alone.

## Verification

[`SwappedSetterThresholdCarry.lean`](../MatrixMortality/SwappedSetterThresholdCarry.lean)
contains the signed swapped-code algebra, the exact digit carry equivalence, its finite interval,
the erasure and rule macro steps, the target cross-product adapter, the common-erasure
divisibility theorem, and the halting consequence. The module builds warning-free, its namespace
passes all default environment linters, and its publication-facing declarations are listed in
`AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterThresholdCarry.lean`](../MatrixMortality/SwappedSetterThresholdCarry.lean)
- [`MM-S57`](../SALVAGE.md#mm-s57-centered-history-defect-transport)
- [`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
