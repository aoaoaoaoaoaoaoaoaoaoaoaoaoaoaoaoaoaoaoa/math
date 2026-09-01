# Full-Tail Last-Step Resonance Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every nonterminal full-erasure-tail pole forces the last history block's upper
length to equal one plus the discarded common three-adic depth

[`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry) proves that a full
`β`-erasure target tail forces the primitive carrier gap to be divisible by `ρ=3^β`.
[`MM-S61`](../SALVAGE.md#mm-s61-primitive-carrier-gap-no-go) shows that this congruence occurs
on reachable carriers, so it cannot itself exclude a pole. This audit couples the congruence to
the exact normalization of the final history step.

## Raw Normalization

Let primitive `(n,d)` precede the last completed block `z`. Its exact raw successor is

```text
N=H((P_z−μA_z)d−V_zn),
D=R(P_zd−V_zn),                                        (1)
```

where `A_z=3^a` and `a=upperLength(z)`. Normalize by a common nonzero integer `s`:

```text
N=s n',      D=s d',      gcd(n',d')=1.                (2)
```

Suppose `(n',d')` reaches a nonterminal target pole whose final `β` tiles are erasures. The
target cross-product and common suffix give

```text
ρ ∣ d'−n',      d'−n'≠0.                               (3)
```

Because `(n',d')` is primitive, (3) makes `d'` a `3`-adic unit.

## Predecessor Unit

The predecessor denominator is also a unit. Assume instead that `3∣d`. Primitivity makes `n`
a unit, and the physical lower code `V_z` is a unit. Therefore

```text
E=P_zd−V_zn                                                (4)
```

is a unit. The denominator equation `D=RE=s d'` makes `s` a unit. In the raw gap identity

```text
s(d'−n')=μ(H A_zd−3E),                                  (5)
```

the first term inside the parentheses has depth at least two, while the second has depth one.
The right side therefore has exact depth one. The left side has depth at least `β≥2` by (3), a
contradiction.

## Forced Resonance

Put

```text
g=v₃(s),      h=v₃(d'−n').                              (6)
```

Since `R` and `d'` are units, the denominator equation gives `v₃(E)=g`. The two terms inside
(5) now have exact depths

```text
a,      g+1.                                            (7)
```

The complete left side of (5) has depth `g+h`, with `h≥β≥2`. If the depths in (7) differed,
their minimum would survive and would be strictly smaller than `g+h`. They must therefore be
equal:

```text
upperLength(z)=v₃(s)+1.                                 (8)
```

Lean constructs `g` from the exact integer valuation of `s`; no chosen shell or hidden unit
hypothesis remains in the final theorem.

## Boundary

The result requires primitive predecessor and successor coordinates, their exact normalization
equations (2), a live successor denominator, and a nonterminal pole against a target with a full
`β`-erasure tail. It does not bound `v₃(s)`, exclude equality (8), use earliestness, or classify
other target suffixes. The remaining full-tail obstruction is exact: prove that a physical last
step cannot cancel precisely `a−1` powers of three, or combine that forced shell with the
multiplicative suffix carry. No `M₅(3)` conclusion follows.

## Verification

[`SwappedSetterCarrierResonance.lean`](../MatrixMortality/SwappedSetterCarrierResonance.lean)
contains the primitive congruence-unit theorem, automatic predecessor-unit proof, raw
normalization balance, and the physical full-erasure-tail pole adapter. The supporting direct
divisibility theorem is in
[`SwappedSetterThresholdCarry.lean`](../MatrixMortality/SwappedSetterThresholdCarry.lean). Both
modules build warning-free; the new namespace passes all default environment linters, and the
publication-facing declarations are listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterCarrierResonance.lean`](../MatrixMortality/SwappedSetterCarrierResonance.lean)
- [`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry)
- [`MM-S61`](../SALVAGE.md#mm-s61-primitive-carrier-gap-no-go)
- [`MM-S63`](../SALVAGE.md#mm-s63-full-tail-last-step-resonance)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
