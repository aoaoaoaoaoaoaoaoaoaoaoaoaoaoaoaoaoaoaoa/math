# Short All-`c` Three-Block Shell Audit

**Date:** 2026-09-01
**Target:** exact discrepancy depths for short all-`c` currents above the decimal `R_c` root
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every width through `β+2` has a checked mixed-prime grammar; only the
`D_b`, width-`β+2` two-adic residual remains unresolved

## Classification

Let `n` be the all-`c` current width and `k` the intervening upper length. For `n≤β`, the pole
equation forces discrepancy shell

```text
(v₂δ,v₅δ)=(k+β+1−n,k+β−n).
```

At `n=β+1`, an explicit normalized residue `2 mod 5` excludes equal-depth cancellation and
gives `(k,k−1)`. At `n=β+2`, the five-depth is always `k−1`. If the singleton target is `D_c`,
the normalized two-coefficient is `2 mod 4`, so the full shell reverses to `(k−2,k−1)`.

For target `D_b` at `n=β+2`, Lean proves the exact coefficient factorization
`2^(β+4)·C`. No phase-independent theorem presently proves `C≠0` or fixes its two-adic depth.

## Scope

The theorems assume `β≥3`, a multi-role erasure-ended current whose letters are all `c`, an
arbitrary body and intervening block, and an actual three-block singleton pole. They classify
necessary discrepancy depths; they do not assert pole reachability.

## Verification

The module and selected namespace lint compile without warnings. Lean LSP reports no
diagnostics. The forbidden-aperture scan and whitespace check are empty. Publication-facing
theorems depend only on the reviewed standard axiom set.

## Artifacts

- [`DecimalSetterThreeBlockShortCurrent.lean`](../MatrixMortality/DecimalSetterThreeBlockShortCurrent.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s97-short-all-c-three-block-shell-grammar)
