# One-`R_b` Root Sign Extinction Audit

**Date:** 2026-08-31
**Target:** the remaining one-role shallow source of the decimal setter
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** `[R_b]` cannot hit any shallow pole; together with the `[R_c]` normalization this
completely classifies one-role shallow sources

## Exact Complement

The upper spelling of `[R_b]` is the long tag `1·0^β·1`. Appending the marker and subtracting
from the exact ambient decimal length gives

```text
9Δ_[R_b] = −(502·10^β−7) = −lift(10^β).
```

The proof uses the canonical long-tag and marker code identities; it does not infer the sign
from numerical examples or floating-point bounds.

## Sign Wall

For `β>0`, `10^β≥10`, hence both physical constants `gap(10^β)` and `lift(10^β)` are positive.
The punctuated upper code of every target and of `[R_b]` itself is a positive natural code cast
to the rationals. Every target lower code is nonnegative. Therefore the generalized equation

```text
gap·P·H = lift·V·Δ
```

has a strictly positive left side and a nonpositive right side. Lean proves contradiction
without assuming the target is nonempty or parser-lawful.

## One-Role Classifier

There are only two one-role rule roots. Case splitting on their tag letter and composing the
sign extinction with `MM-S81` yields

```text
HitsSquarePole β body target [[R_letter]]
↔ letter=c ∧ terminalMatch(target).
```

Thus all malformed shallow poles must have a source block of length at least two. This does not
classify those longer roots, singleton targets, or deep histories.

## Verification

The module and root aggregate build without warnings. Dedicated default lint and Lean LSP
diagnostics are clean. The selected transitive axiom audit contains only the reviewed standard
axioms. Forbidden-form and diff checks pass; no proof aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterMinimumBody.lean`](../MatrixMortality/DecimalSetterMinimumBody.lean)
- [`DecimalSetterBridge.lean`](../MatrixMortality/DecimalSetterBridge.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s82-one-r_b-root-sign-extinction)
