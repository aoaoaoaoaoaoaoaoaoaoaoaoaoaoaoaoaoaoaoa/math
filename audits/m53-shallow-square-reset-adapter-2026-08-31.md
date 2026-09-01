# Shallow Square-Reset Adapter Audit

**Date:** 2026-08-31
**Target:** the one-root shallow branch of the decimal `M₅(3)` bridge frontier
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the matrix pole has an exact generalized raw-head equation and both root factors
are decimal units; identification with the distinguished peeled two-`c` head remains unproved

## Equation

For a source role block, define

```text
H = code(spell upper source · marker),
Δ = μ·10^|spell upper source| − H.
```

`bridgeState_single_eq` computes the unsquared root state as

```text
[H/μ, 0, Δ/(μ·basisGap)].
```

Applying `squareReset` and an arbitrary target block gives the exact first coordinate

```text
(basisGap·P·H − alpha·V·Δ)/(μ²·basisGap),
```

where `P` and `V` are the target's punctuated upper and complete lower codes. The denominator is
nonzero for `β>0`. The checked calibrations

```text
9μ·basisGap = gap(10^β),
9μ·alpha    = lift(10^β)
```

therefore prove, in both directions,

```text
HitsSquarePole target [source]
↔ gap(10^β)·P·H = lift(10^β)·V·Δ.
```

## Unit Shells

For `β>0`, the marker ends in `false`, whose decimal digit is seven. Thus every `H` ends in
seven. A parser-lawful source satisfies `EndsInRule`, so it is nonempty and its upper spelling
has positive length. The term `μ·10^|upper|` is then zero modulo ten, while `H` is seven modulo
ten; consequently `Δ` is three modulo ten. Lean proves exact shell `(0,0)` for both factors.

The reusable digit lemmas now live at their semantic owners:
`DecimalSetterArithmetic` owns the decimal-three/seven integer-unit rules, and
`DecimalSetterCarry` owns the code-ending-seven congruence and unit theorem. Their former local
duplicates in the phase and suffix modules were removed.

## Boundary

This result is not the distinguished first-entry extinction. `MM-S67` consumes
`code(peeledHeadWord β (c::c::tail))` and the complement `10μ−H`. The parser root here is the
full punctuated upper spelling of an arbitrary rule-ended role block, and its complement uses
the whole upper length. The unit shells alone do not identify these parameters or exclude the
equation. Singleton targets and histories with at least two source blocks remain separate
`MM-S74` branches.

## Verification

The arithmetic, carry, phase, suffix, bridge, and root aggregate modules build without warnings.
The selected transitive axiom audit contains only the reviewed standard axioms. Forbidden-form
and diff checks pass. No proof aperture or linter suppression is present.

## Artifacts

- [`DecimalSetterBridge.lean`](../MatrixMortality/DecimalSetterBridge.lean)
- [`DecimalSetterArithmetic.lean`](../MatrixMortality/DecimalSetterArithmetic.lean)
- [`DecimalSetterCarry.lean`](../MatrixMortality/DecimalSetterCarry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s77-shallow-generalized-raw-head-adapter)
