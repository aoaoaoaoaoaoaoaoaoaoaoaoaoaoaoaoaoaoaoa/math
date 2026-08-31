# Decimal Setter Gap-Factor Ancestry Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every gap-clean denominator-descended carrier hitting a singleton must pass two
exact code congruences; gap-contaminated ancestry and the surviving quotient language remain
open

This audit intersects the abstract long singleton carriers of
[`MM-S20`](../SALVAGE.md#mm-s20-singleton-carrier-classification) with the denominator ancestry
of [`MM-S17`](../SALVAGE.md#mm-s17-recursive-decimal-carrier). It does not settle `M₅(3)`.

## Physical Factors

For width `β>0`, put

```text
q=2·10^β−7,       E=9q,       G=502·10^β−7.
```

The power `10^β` is one modulo nine, so `G=9g` for an integer `g`. The primitive gap factor is
coprime to the lift and to the lower digit of either singleton erasure:

```text
gcd(q,G)=gcd(q,7)=1.                              (1)
```

For the first equality, `G=251q+1750`. The integer `q` is odd, is three modulo five, and is
coprime to seven because `10` is; hence it is coprime to `1750=2·5³·7`. Both singleton
erasures have lower word `[false]`, whose decimal code is `7`.

## First Gate

Choose a common integral representative of the finite recursive carrier segment. Write the
current carrier as `(N,D)` and retain the preceding numerator in the exact denominator law

```text
D=EN₋.                                            (2)
```

For current and singleton-target upper/lower codes, write

```text
T₂=EP₂+GV₂,       T₃=EP₃+7G.                     (3)
```

The next-pole equation is

```text
(NT₂−10μGV₂D)T₃=EμG10^mN·7.                      (4)
```

Modulo `q`, equations (2)--(4) give

```text
q ∣ NG²V₂·7.                                      (5)
```

If the integral representative is gap-clean, meaning `gcd(q,N)=1`, then (1) cancels every
factor except the current lower code:

```text
V₂=qW.                                            (6)
```

This first gate alone is not a closure theorem. Compiler-emitted lower words can in principle
carry the gap factor.

## Quotient Gate

Substitute `E=9q`, `G=9g`, (2), (3), and (6) into (4). Cancelling the exact common factor
`81q` leaves

```text
[N(P₂+gW)−90μgqWN₋](qP₃+7g)=μg10^mN·7.           (7)
```

Reduction modulo `q` and the same coprimality cancellation now force

```text
q ∣ P₂+gW−μ10^m.                                  (8)
```

Equation (8) is not visible to the two/five-adic shell calculus saturated by `MM-S20`. It uses
both recursive denominator ancestry and the compiler's integral upper/lower trace form.

## Exact Boundary

The theorem removes every gap-clean carrier/current-code pair that fails either (6) or (8), at
every sign and length. It covers both singleton targets because their lower code is the same.
It does not prove that `q` stays coprime to every reachable carrier numerator, and it does not
yet classify compiler-emitted pairs satisfying the quotient congruence.

The remaining physical multi-to-singleton seam is therefore the disjunction:

1. a reachable primitive carrier acquires `q∣N`; or
2. a compiler-emitted block has `V₂=qW` and satisfies (8).

This is a strict reduction of the `m≥β+3` abstract carrier branch, not a proof of mortality
avoidance and not a false pole.

## Verification

`DecimalSetterAncestry.lean` proves the fixed coprimalities, exact modular product reduction,
factor cancellation, and quotient congruence. The module is warning-free and uses no proof
apertures. Its publication-facing theorem is included in `AxiomAudit.lean`; the reviewed
transitive axiom set is recorded in `verification/axioms.txt`.

## Artifacts

- [`DecimalSetterAncestry.lean`](../MatrixMortality/DecimalSetterAncestry.lean)
- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s22-gap-factor-quotient-gate)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
