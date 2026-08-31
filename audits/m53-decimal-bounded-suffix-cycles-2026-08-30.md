# Decimal Setter Bounded-Suffix Cycle Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every emitted multi-role block has a compatible carrier self-loop at every bounded
decimal precision; fixed-modulus acyclicity cannot prove projective avoidance

This audit concerns the generalized carrier after a surviving distinguished-reset entry. It
does not construct an exact rational cycle, prove reachability from that entry, or settle
`M₅(3)`.

## Stationary Defect

Write a multi-role trace as `T=10τ`. For a block of upper length `m≥3`, put `h=m−2`. On a
carrier with denominator one and numerator `x`, division of

```text
R=xT−10μGV
```

by ten leaves `τx−μGV`. If this is `10^hN′`, the next denominator is `D′=Ex`. Equality
of the old and new projective ratios would require `N′=xD′=Ex²`; its defect is therefore

```text
F(x)=10^hEx²−τx+μGV.                              (1)
```

The emitted residues are

```text
E≡7,       τ≡1,       μ≡7,       G≡3,       V≡7  (mod 10).
```

Thus `F(7)≡0 (mod 10)`, while `F′(x)≡−1 (mod 10)` because `h≥1`.

## Explicit Lift

Suppose `F(x)=10^kq`. Define

```text
y=x+q10^k.
```

Writing `10^hE=10a` and `τ=1+10b`, direct expansion gives

```text
F(y)=10^k·10q(−b+2ax+aq10^k).                           (2)
```

Consequently `y≡x (mod 10^k)` and `10^(k+1)∣F(y)`. Starting at `x=7` and iterating (2)
constructs a coherent stationary root through every power of ten. It is unique at each
precision: the difference of two defects factors as

```text
F(x)−F(y)=(x−y)(10^hE(x+y)−τ),
```

and the second factor is `−1` modulo ten, hence coprime to `10^k`. This is the elementary
composite-radix form of a derivative-unit lift; no completeness or external `p`-adic theorem is
used.

## Recurrence Consumer

Choose a root modulo `10^(h+k)`, so

```text
F(x)=10^(h+k)e.
```

Set

```text
N′=Ex²−10^k e,       D′=Ex.
```

Equation (1) now yields the exact carrier factorization

```text
τx−μGV=10^hN′,                                  (3)
```

and the stationary projective congruence

```text
N′≡xD′ (mod 10^k).                                (4)
```

The residue laws also give `x≡7` and `D′≡9 (mod 10)`, so both carrier coordinates remain
decimal units. Hence every individual physical multi-role block contributes a projective
self-loop to every bounded decimal-suffix transition graph.

## Exact Boundary

The carrier selected at precision `k` may change with `k`. The coherent residues determine a
formal decimal inverse-limit address, but this audit does not identify that address with a
rational number, an integer, or a state reached from the distinguished raw head. A finite
recognizer may still succeed by retaining encoded-entry reachability or semantic information
beyond the residue pair.

The result excludes only proofs that demand acyclicity or strict descent on all unit carriers
modulo one fixed power of ten. The next live problem is whether the encoded-entry suffix
language intersects any compatible inverse-limit address.

## Verification

`cycleDefect_lift` formalizes (2), `cycleDefect_roots_congruent` proves uniqueness at each
precision, `exists_cycleDefect_root` performs the induction,
`peeledNumerator_factor` restores the literal residual `R=10^(h+1)N′`, and
`emittedBlock_exists_approximate_cycle` composes the roots with (3)–(4). The narrow module build
and Lean language-server diagnostics pass without warnings, suppressions, or proof apertures.
The publication-facing declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Artifacts

- [`DecimalSetterSuffix.lean`](../MatrixMortality/DecimalSetterSuffix.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s21-bounded-decimal-suffix-cycles)
- [`m53-decimal-recursive-carrier-2026-08-30.md`](m53-decimal-recursive-carrier-2026-08-30.md)
