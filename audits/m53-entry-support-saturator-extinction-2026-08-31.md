# Entry Support-Saturator Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the universal all-`D_c` gap-support saturator exists in the lower-code language but
cannot be the first transition from a lawful two-`c` raw head to another multi-role pole

This audit composes the language-saturation theorem
[`MM-S28`](../SALVAGE.md#mm-s28-arbitrary-history-gap-support-saturation) with the raw-head
extinction theorem [`MM-S19`](../SALVAGE.md#mm-s19-all-deletion-raw-head-extinction). It does
not exclude other support-saturating words or later generalized carriers and does not settle
`M₅(3)`.

## Entry Width

For deletion width `β>0`, put

```text
q=2·10^β−7,
e=φ(|q|),
n=3e.
```

The primitive gap is positive, hence `e>0` and `n≥3`. The all-erasure lower spelling of width
`e` is `0ᵉ`; its decimal code is divisible by `q` by Euler's theorem. The width-`n` spelling is
the concatenation of three copies of `0ᵉ`. Decimal code concatenation preserves divisibility by
`q`, so

```text
q ∣ code(0ⁿ).                                     (1)
```

Thus `D_cⁿ` saturates the full primitive gap, not only its radical. Tripling changes no source
grammar: every letter remains the physical erasure tile `D_c`, and its lower side remains
independent of the compiler body.

## Raw-Head Exclusion

Let `H` be the decimal code of a lawful decimal-unit two-`c` raw head. For the all-`D_c` block
of length `n`, write its upper and lower codes as `P,V`, its trace as `T=EP+GV`, and its
initial residual as

```text
R=HT−10μGV.
```

The exact code identities are

```text
9P=50·10^β·10ⁿ+2·10^β−7,
9V=7·10ⁿ−7.                                      (2)
```

A transition to another multi-role pole requires `R` to have decimal shell `(n−1,n−1)`.
Because `n≥3`, the hypotheses in (2) lie exactly in the scope of
`allCDeletion_peeledDoubleCHead_shell_impossible`. That theorem contradicts the required shell
for every `β≥2` and every lawful two-`c` raw head. Therefore the support-saturating block from
(1) is absent from the first multi-role transition grammar.

## Exact Boundary

The theorem excludes only `D_c^(3φ(|q|))` at the distinguished raw-head entry. It does not
exclude:

- rule-bearing support-saturating first blocks;
- all-erasure first blocks containing `D_b`;
- transitions to a singleton target; or
- the same all-`D_c` block after a generalized product-residual carrier.

The result is therefore an encoded-entry cut, not a global language obstruction. It proves that
the body-independent support witness cannot itself connect the distinguished entry to the
recursive multi-role corridor. Further progress must retain the actual first-block grammar or
extend raw-head extinction to generalized carriers.

## Verification

`DecimalSetterAncestry.lean` proves positivity of the entry width, full-gap divisibility of the
literal physical lower code, its exact decimal identity, and the raw-head shell contradiction.
The module is warning-free and contains no proof aperture. The publication-facing theorems are
listed in `AxiomAudit.lean`; their reviewed transitive axiom sets are recorded in
`verification/axioms.txt`.

## Artifacts

- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`MM-S19`](../SALVAGE.md#mm-s19-all-deletion-raw-head-extinction)
- [`MM-S28`](../SALVAGE.md#mm-s28-arbitrary-history-gap-support-saturation)
- [`MM-S32`](../SALVAGE.md#mm-s32-entry-support-saturator-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
