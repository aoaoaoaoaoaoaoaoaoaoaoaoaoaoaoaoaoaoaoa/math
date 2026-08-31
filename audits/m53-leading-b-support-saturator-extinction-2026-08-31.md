# Leading-`D_b` Support-Saturator Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the full-gap-saturating block `D_bD_c^(3φ(|q|)−1)` cannot be the first
transition from a lawful two-`c` raw head to another multi-role pole

This audit extends the all-`D_c` entry exclusion
[`MM-S32`](../SALVAGE.md#mm-s32-entry-support-saturator-extinction) to the first pure-erasure
family containing `D_b`. It does not decide other `D_b` placements, rule-bearing blocks, or
later generalized carriers, and does not settle `M₅(3)`.

## Physical Codes

For deletion width `β>0`, put

```text
q=2·10^β−7,
n=3φ(|q|).
```

The block `D_bD_c^(n−1)` contains `n` erasure tiles. Both `D_b` and `D_c` spell the one-digit
lower word `0`, so its complete lower spelling is `0ⁿ`, exactly the lower spelling of `D_c^n`.
The code established in `MM-S32` therefore gives

```text
q ∣ lowerCode(D_bD_c^(n−1)).                    (1)
```

On the upper side, the `b` tag is the marker word followed by the one bit contributed by a
`c` tag. Thus the complete punctuated words satisfy

```text
upper(D_bD_c^(n−1))=marker ++ upper(D_c^n).
```

The all-`D_c` punctuated word has length `n+β+1`. The marker code equals `μ` under the exact
setter calibration `9μ=52·10^β−7`, hence

```text
P_b=P_c+μ·10^(n+β+1).                           (2)
```

These are literal word and decimal-code identities, not an abstract trace hypothesis.

## Five-Adic Exclusion

Let `H` be any lawful decimal-unit two-`c` raw head. For the all-`D_c` word of arbitrary
positive width `n`, write

```text
R_c=H(E P_c+G V)−10μGV.
```

`DecimalSetterFiveDepth.lean` proves

```text
5^(n+β) ∤ R_c.                                  (3)
```

For a regular terminal run `1≤s≤β−2`, the exact residual decomposition has three possible
least five-adic exponents: `s+1`, `n`, and `β`. Their coefficients are nonzero modulo five;
when `n=s+1`, the tied coefficient is also nonzero. For the exceptional run `s=β−1`, the
decomposition reduces to terms at exponents `n+1` and `2β`. Separate proofs cover
`n+1<2β`, equality, and `2β<n+1`; the equality coefficient is nonzero modulo five. These
cases exhaust the raw-head grammar supplied by `peeledDoubleCHead_unit_shape`.

For the leading-`D_b` word, equation (2) changes the residual by

```text
R_b−R_c=HEμ·10^(n+β+1).                         (4)
```

The right side of (4) is divisible by `5^(n+β)`. A multi-role target after the longer upper
word requires `R_b` to have decimal shell `(n+β,n+β)`, and therefore requires the same power
of five to divide `R_b`. Subtracting (4) would make `5^(n+β)` divide `R_c`, contradicting (3).

## Exact Boundary

The formal theorem excludes the physical block `D_bD_c^(3φ(|q|)−1)` only at the distinguished
raw-head entry. It leaves open:

- a pure-erasure saturator whose `D_b` occurs later;
- every rule-bearing support saturator;
- transitions to singleton targets; and
- any saturator applied after a reachable generalized product residual.

No claim is made from the broader mixed-erasure computation. Further progress must prove the
remaining exact source grammar or move the five-adic exclusion beyond the raw-head carrier.

## Verification

`DecimalSetterFiveDepth.lean` proves the arbitrary-width divisibility obstruction and its
marker-perturbation consequence. `DecimalSetterAncestry.lean` proves the physical lower and
upper identities, full-gap saturation, and entry composition. Both modules build under the
strict project lints without a proof aperture. Publication-facing theorem axiom sets are
listed in `AxiomAudit.lean` and recorded in `verification/axioms.txt`.

## Artifacts

- [`DecimalSetterFiveDepth.lean`](../MatrixMortality/DecimalSetterFiveDepth.lean)
- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`MM-S28`](../SALVAGE.md#mm-s28-arbitrary-history-gap-support-saturation)
- [`MM-S32`](../SALVAGE.md#mm-s32-entry-support-saturator-extinction)
- [`MM-S33`](../SALVAGE.md#mm-s33-leading-d_b-support-saturator-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
