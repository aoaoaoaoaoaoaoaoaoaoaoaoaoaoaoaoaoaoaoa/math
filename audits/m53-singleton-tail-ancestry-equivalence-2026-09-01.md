# Singleton-Tail Ancestry Equivalence Audit

**Date:** 2026-09-01
**Target:** unit peeled ancestry on arbitrary lawful tails of the decimal singleton frontier
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** at an actual singleton pole, older unit ancestry is equivalent to a multi-role
current block with at least `β+3` upper digits

## Ray Nondegeneracy

Every parser-lawful block history has nonzero homogeneous ray. The rightmost root has nonzero
first coordinate. At each recursive step, a nonzero older first coordinate makes the new second
coordinate nonzero. If the older first coordinate vanishes, the inductive ray nonvanishing gives
a nonzero second coordinate; the erasure boundary makes the lower code nonzero, so the new first
coordinate is nonzero.

## Reverse Shell

For an actual singleton pole above current block data `(T,V,A)` and older ray `(x,y)`, the
uncancelled recurrence is

```text
(Tx−lift·Vy)S=gap·μ·lift·A·x·7.                       (1)
```

The tail ray cannot vanish, and (1) excludes `x=0`. With `A=10^m`, division gives

```text
y/x = (T−R)/(lift·V),
R   = gap·μ·lift·10^m·7/S.                            (2)
```

For a multi-role erasure-ended current, `T` has decimal shell `(1,1)`. The singleton trace `S`
has shell `(β+1,β)`, so `R` has shell `(m−β−1,m−β)`. When `m≥β+3`, both entries are strictly
deeper than one. Exact unequal-valuation subtraction fixes `T−R` at `(1,1)`, and `lift·V` is a
unit. Thus the quotient in (2) has shell `(1,1)`. The intrinsic quotient criterion constructs
the required unit peeled coordinates.

## Exact Equivalence

The earlier forward carrier theorem says unit peeled ancestry forces the current block to have
at least two roles and `m≥β+3`. Combining both directions yields

```text
AdmitsUnitPeeledCarrier(older ray)
  ↔ length(current)≥2 and m≥β+3.
```

Because an erasure-ended current is nonempty, negating the equivalence gives the exact residual
grammar: the current is a singleton, or it is multi-role with `m≤β+2`.

## Boundary

The result assumes `β≥3`, an actual singleton pole, an erasure-ended current, and parser law on
the nonempty older tail. It does not exclude the short residual grammar. On the long branch it
constructs rational unit coordinates, not the integral denominator recurrence or common-suffix
factorization required by the denominator-ancestry quotient gates.

## Verification

The dedicated module and root aggregate build without warnings. Namespace lint and Lean LSP
diagnostics are clean. The full axiom audit compiles, and every selected declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`. No proof aperture, external declaration,
unsafe definition, or linter suppression is present.

## Artifacts

- [`DecimalSetterSingletonAncestry.lean`](../MatrixMortality/DecimalSetterSingletonAncestry.lean)
- [`DecimalSetterBridgeRay.lean`](../MatrixMortality/DecimalSetterBridgeRay.lean)
- [`DecimalSetterRootRay.lean`](../MatrixMortality/DecimalSetterRootRay.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s90-exact-singleton-tail-ancestry-equivalence)
