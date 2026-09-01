# `R_c`-Root Singleton-`D_c` Extinction Audit

**Date:** 2026-09-01
**Target:** the singleton `D_c` pole over exactly two parser source blocks
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no parser-lawful two-block source reaches this pole for `β≥3`

## Exact Equation

Record `MM-S86` proves that any singleton pole over two lawful source blocks has root exactly
`R_c`, a multi-role current block, and current upper length `m≥β+3`. The `D_c` singleton trace
and `R_c` root calibrations reduce the uncancelled physical recurrence to the equivalence

```text
HitsSquarePole D_c [current,R_c]
  ↔ 2·10^β(P−V)=7μ·10^m,                              (1)
```

where `P` is the punctuated current upper code, `V` is the current lower code, and `μ` is the
marker code. This equivalence needs no parser law; parser law enters only through the S86 shape
classifier.

## Suffix Contradiction

Set `w=m−β−1`. The lower bound on `m` gives `w>0`, and cancellation in (1) gives

```text
P−V=35μ·10^w.                                         (2)
```

The marker is nonempty and has odd terminal digit, so `μ` is odd. Equation (2) makes `10^w`
divide `P−V` but excludes divisibility by `2·10^w`. The exact suffix-exhaustion theorem then
identifies the lower word with the length-`w` suffix of the punctuated upper word. The code of
the complementary prefix is consequently `35μ`.

The punctuated upper word has length `m+β+1`; removing `w=m−β−1` digits leaves a prefix of
length `2β+2`. Every upper alphabet digit is at least five, hence that prefix code is at least
`5·10^(2β+1)`. On the other hand, `μ<10^(β+1)` and `β≥3` imply

```text
35μ < 5·10^(2β+1).
```

These bounds are incompatible. The proof uses the physical lower spelling directly; it does not
assume reachability beyond `BlocksLaw [current,R_c]`.

## Boundary

The result closes the `D_c` target arm only. The `D_b` target has a different singleton trace
coefficient, so its fixed-root discrepancy does not reduce to (2). Singleton poles with more
than two source blocks also remain outside because their older parser ray need not be a physical
root ray.

## Verification

The dedicated module and root aggregate build without warnings. Namespace lint and Lean LSP
diagnostics are clean. The full axiom audit compiles, and every selected declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`. No proof aperture, external declaration,
unsafe definition, or linter suppression is present.

## Artifacts

- [`DecimalSetterRuleCRootSingleton.lean`](../MatrixMortality/DecimalSetterRuleCRootSingleton.lean)
- [`DecimalSetterRootRay.lean`](../MatrixMortality/DecimalSetterRootRay.lean)
- [`DecimalSetterCarry.lean`](../MatrixMortality/DecimalSetterCarry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s88-r_c-root-singleton-d_c-extinction)
