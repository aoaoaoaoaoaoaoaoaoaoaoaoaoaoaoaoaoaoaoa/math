# Two-C Singleton-B Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the `cc→D_b→singleton` branch of the swapped-ternary first multi-transfer gate is
empty

This audit attacks the third branch isolated by
[`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy). It does not address the other
two branches or later multi-transfer histories.

## Phase Erasure

The first block has two roles with underlying letters `cc`; each role may independently be in
its rule or erasure phase, subject to the final-erasure block grammar. The centered state after
the first transfer from reset zero depends here only on the upper spelling. Lean proves

```text
upper length = 2,
punctuated swapped upper code = 14ρ−1,       ρ=3^β.       (1)
```

Thus the lower phase choices and the compiler body disappear from this branch before the
singleton `D_b` transfer.

## Exact Factors

The swapped singleton coefficients are

```text
C_b=−ρ(18ρ²−40ρ+17),
C_c=−ρ(5ρ−1),
K=(2−ρ)(5ρ−1)(2ρ−1).
```

Substituting (1) into the centered recurrence, applying `D_b`, and then imposing the next
singleton pole gives the two left sides

```text
E_c=−ρ(ρ−2)²(5ρ−1)(252ρ³−578ρ²+238ρ−9),

E_b=−ρ(ρ−2)²
    (4536ρ⁵−11412ρ⁴+3824ρ³+2848ρ²−1588ρ+171).  (2)
```

For the admissible range `β≥3`, `ρ≥27`. Writing `t=ρ−27` turns the two residual
polynomials into

```text
252t³+19834t²+520150t+4545171,

4536t⁵+600948t⁴+31838768t³+843217384t²
  +11163107588t+59099138739.                              (3)
```

Every term in (3) is nonnegative and each constant is positive. The remaining factors in (2)
are positive before the leading minus sign. Hence `E_c<0` and `E_b<0`, contradicting either
prospective pole equation `E=0`.

## Exact Boundary

The theorem is uniform in the source body and the two initial phases. It uses the physical
swapped coefficients and therefore excludes exactly the third `MM-S35` branch. It does not
classify `cc→multi`, `c^(β+1)→singleton`, or any later history. The analogous decimal result is
separate because its centered recurrence and shell arithmetic use radix ten and two primes.

## Verification

[`SwappedSetterMultitransfer.lean`](../MatrixMortality/SwappedSetterMultitransfer.lean) proves
the phase-independent code identities, exact factorization, shifted polynomial positivity, and
the contradiction for both target letters. The module is warning-free, passes the default
environment linter, and contains no proof aperture. Its publication-facing declarations are
listed in `AxiomAudit.lean`; the canonical snapshot is regenerated after concurrent integration.

## Artifacts

- [`SwappedSetterMultitransfer.lean`](../MatrixMortality/SwappedSetterMultitransfer.lean)
- [`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy)
- [`MM-S38`](../SALVAGE.md#mm-s38-two-c-singleton-b-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
