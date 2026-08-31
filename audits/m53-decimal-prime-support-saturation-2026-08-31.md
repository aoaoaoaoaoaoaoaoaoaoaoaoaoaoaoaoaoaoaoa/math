# Decimal Setter Prime-Support Saturation Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** gap-prime support has an exact arbitrary-history law, but the physical lower-code
language contains a code divisible by the full primitive gap; no permanently absent gap factor
can obstruct the setter

This audit extends the one-step factor ancestry in
[`MM-S24`](../SALVAGE.md#mm-s24-factorwise-gap-ancestry). It does not prove that a
support-saturating word is reachable from the distinguished carrier and does not settle
`M₅(3)`.

## Exact Histories

For width `β>0`, put `q=2·10^β−7`. A certified carrier step from numerator `N` through lower
code `V` to numerator `N'` retains witnesses for

```text
D=EN₋,
T=EP+GV,
NT−10μGVD=10^dN'.
```

For every prime `p∣q`, the one-step theorem gives

```text
p∣N'  ↔  p∣N or p∣V.                             (1)
```

`GapCarrierHistory` composes these certified steps while recording the emitted lower codes.
Induction on the history proves

```text
p∣Nₖ  ↔  p∣N₀ or p∣Vᵢ for some 1≤i≤k.            (2)
```

Thus an initially absent prime enters if and only if it divides an emitted lower code in the
actual history. The theorem has no fixed history-length bound.

Define saturated gap support by `rad(q)∣N`. The generic radical factorization theorem and
positivity of `q` identify this with divisibility by every prime `p∣q`. Combining that
equivalence with (2) gives

```text
rad(q)∣Nₖ
  ↔ every p∣q divides N₀ or some emitted Vᵢ.       (3)
```

Equation (3) is the exact support condition for disabling all factorwise gates. It does not
discard multiplicities from any quotient gate; it only identifies when every prime-support
gate has disappeared.

## Language Saturation

The lower-code language itself is fully saturated. Let

```text
n=φ(|q|).
```

The primitive gap is positive and coprime to ten. Euler's theorem therefore gives

```text
q∣10ⁿ−1.                                          (4)
```

Consider the physical ordinary-tile block `D_cⁿ`. Every erasure tile has lower word `[0]`, so
the block's lower spelling is `0ⁿ`, independent of the compiler body. If `Cₙ` is its decimal
code, the exact repeated-zero identity is

```text
9Cₙ+7=7·10ⁿ,
9Cₙ=7(10ⁿ−1).                                    (5)
```

Every divisor of `q` is coprime to nine. Equations (4) and (5) therefore imply

```text
q∣Cₙ,
rad(q)∣Cₙ.                                        (6)
```

The stronger full-gap divisibility in (6) needs no factorization of `q` and holds for every
`β>0` and every compiler body.

## Exact Boundary

Equations (2) and (3) are reachability statements only after a `GapCarrierHistory` witness has
been supplied. Equation (6) supplies a physical source word and its lower code, but not such a
history. It does not prove that the distinguished raw head reaches a carrier on which `D_cⁿ`
is an exact next step, nor that the resulting carrier reaches a singleton pole.

The result therefore rejects each proposed invariant of the form “some prime factor of `q`
never occurs in an emitted lower code.” It does not reject an invariant coupling carrier state
to the current upper code, quotient congruence, or complete inverse suffix address. Those joint
coordinates own the remaining problem.

## Verification

`DecimalSetterAncestry.lean` defines the exact step and history relations, proves (2) and (3),
spells the all-erasure block, and proves both divisibilities in (6). The module is warning-free
and contains no proof aperture. The publication-facing theorems are listed in `AxiomAudit.lean`;
their reviewed transitive axiom sets are recorded in `verification/axioms.txt`.

## Artifacts

- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`MM-S24`](../SALVAGE.md#mm-s24-factorwise-gap-ancestry)
- [`MM-S26`](../SALVAGE.md#mm-s26-exact-raw-head-prime-support)
- [`MM-S28`](../SALVAGE.md#mm-s28-arbitrary-history-gap-support-saturation)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
