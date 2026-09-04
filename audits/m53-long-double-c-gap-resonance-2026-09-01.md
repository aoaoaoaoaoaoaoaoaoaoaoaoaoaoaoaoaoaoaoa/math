# Long Double-`c` Gap-Resonance Audit

**Date:** 2026-09-01
**Target:** exact primitive-gap support on the long `cc` peeled-head chamber
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every absent ambient gap prime is confined to one smaller-gap decimal-period
resonance

## Head Identity

Decimal-unit peeling forces the `cc` head to end in a nonempty run of `s` sevens, where
`1≤s≤β−1`. Writing `q_n=2·10^n−7`, the exact head and marker identities reduce to

```text
9(H−10μ)=q_s−10q_β.                                 (1)
```

The `MM-S101` support product `q_β∣V(H−10μ)` and (1) imply

```text
q_β∣Vq_s.                                           (2)
```

Thus every divisor of `q_β` coprime to `q_s` enters the current lower code `V`.

## Resonance Grammar

For every integer `r` and `s≤β`, Lean proves the exact equivalence

```text
r∣q_β and r∣q_s  iff  r∣q_s and r∣(10^(β−s)−1).    (3)
```

The forward direction uses the fact that `q_β` is coprime to seven; the reverse direction is
the identity

```text
q_β=10^(β−s)q_s+7(10^(β−s)−1).
```

Consequently any prime divisor of `q_β` absent from `V` must divide both `q_s` and the displayed
decimal-period term. Under pairwise coprimality of `q_β` with all smaller `q_s`, (2) forces the
whole ambient gap into `V`.

## Scope

The pole theorem assumes the long `R_c`, multi/multi, `cc` chamber at `β≥3`. Smaller-gap
resonances do occur for some exponents, so this record is an exact finite grammar, not a uniform
coprimality claim and not a pole extinction theorem.

## Verification

The module, aggregate build, selected namespace lint, Lean LSP diagnostics, forbidden-aperture
scan, whitespace check, and axiom audit pass. Every selected theorem depends only on the
reviewed standard axiom set.

## Artifacts

- [`DecimalSetterThreeBlockLongDoubleC.lean`](../MatrixMortality/DecimalSetterThreeBlockLongDoubleC.lean)
- [`DecimalSetterThreeBlockLongSupport.lean`](../MatrixMortality/DecimalSetterThreeBlockLongSupport.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s102-long-double-c-relative-gap-resonance)
