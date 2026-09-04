# Contaminated-Tail Factorwise Pole-Gate Audit

**Date:** 2026-09-01
**Target:** primitive-gap support at a singleton pole over the lawful contaminated tail
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the full gap divides the product of current and inherited lower codes; only factors
absent from inherited support can be cancelled into the current code

## Arithmetic Normalization

Write `q=2·10^β−7`, let `M` be the marker code, `P` the fixed contaminated-root upper code,
`G` the integral lift, and `V` the inherited lower code. The normalized tail quotient has raw
numerator and denominator

```text
num = 90MP,
den = 9P²−11GV.
```

Every divisor of `q` is coprime to the fixed coefficients used in reducing this fraction.
Lean proves that its reduced discrepancy `reduced.den−10·reduced.num` has exactly the same
coprime support modulo a gap divisor as `V`. The corresponding statement is also checked before
rational reduction.

## Pole Product Law

Clearing the singleton-pole recurrence above this tail first gives

```text
q ∣ V_current·(den−10·num).                           (1)
```

The exact marker and upper-code relations reduce the raw discrepancy modulo `q` to `−11GV`.
Both `11` and `G` are units modulo `q`. Combining this with (1) yields

```text
q ∣ V_current·V.                                     (2)
```

No primality or squarefreeness of `q` is used. Therefore, for every divisor `r∣q`,

```text
gcd(r,V)=1  ⇒  r∣V_current.                           (3)
```

For prime `p∣q`, the premise is exactly `p∤V`. This gives the primewise support-transfer theorem.

## Sharp Boundary

The inherited code is not uniformly coprime to `q`. Lean evaluates the lawful width-three body

```text
b b b b c b c c c c
```

and proves that `q=1993` divides the inherited lower code. Thus (2) cannot be cancelled to full
gap divisibility of the current code without an additional hypothesis. The evaluated body is
not asserted to satisfy the pole equation.

## Scope

The fixed tail is `gapContaminatedTail` from `MM-S91`. The product theorem quantifies over every
positive deletion width, body, singleton target, and current block, conditional on an actual
pole. The divisor and prime corollaries use `β≥3`. The result does not prove existence or
extinction of a pole, and it does not yet cover every `cb/cc` head admitted by `MM-S94`.

## Verification

The dedicated module and root aggregate build without warnings. Selected namespace lint, the
full axiom audit, forbidden-aperture scans, and whitespace checks pass. Every selected theorem
depends only on the reviewed standard axiom set. The saturation example is a kernel-checked
closed computation using ordinary reduction, not `native_decide`.

## Artifacts

- [`DecimalSetterContaminatedPoleGate.lean`](../MatrixMortality/DecimalSetterContaminatedPoleGate.lean)
- [`DecimalSetterGapCleanAncestry.lean`](../MatrixMortality/DecimalSetterGapCleanAncestry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s96-contaminated-tail-factorwise-pole-gate)
