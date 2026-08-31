# Decimal Setter Length-Two Carrier Extinction Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no consecutive multi-shell carrier transition has upper length two

This audit removes the exceptional branch left by
[`MM-S17`](../SALVAGE.md#mm-s17-recursive-decimal-carrier). It does not prove arbitrary-depth
projective avoidance or settle `M₅(3)`.

## Forced Shell

Represent the recursive carrier by decimal units `(N,D)` and put

```text
R=NT₂−10μGV₂D.
```

If the following block is a multi-role pole and the current upper length is `m`,
`peeledNumerator_multi_shell` gives

```text
(ν₂(R),ν₅(R))=(m−1,m−1).                         (1)
```

The former exceptional case was `m=2`, where (1) requires `ν₂(R)=1`.

## Two-Adic Cancellation

The current multi-role trace has `ν₂(T₂)=1`, while `N`, `D`, `μ`, `G`, and `V₂` are
`2`-adic units. Dividing the residual by ten gives

```text
R/10=N(T₂/10)−μGV₂D.                              (2)
```

Both terms in (2) are units in `ℚ₂`. Their difference is not a unit. Indeed, if `a`, `b`, and
`a−b` were all units, then `a/b` and `a/b−1=(a−b)/b` would both be units. The theorem
`PadicValuation.odd_prime_of_adjacent_units` would then make the prime two odd, a contradiction.

Thus `R/10` is not a `2`-adic unit, contradicting (1) at `m=2`. Every non-singleton current
block has `m≥2`, so every surviving consecutive multi-shell transition satisfies

```text
m≥3.                                               (3)
```

`peeledNumerator_twoAdic_deepens` formalizes (2), including arbitrary rational signs and
denominators. `peeledMultiPole_length_ne_two` composes it with (1), and
`peeledMultiPole_three_le_length` proves (3).

## Carrier Audit

No integrality assumption is used. The initial distinguished suffix peel supplies decimal-unit
coordinates. The denominator update `(N,D)↦(N',EN)` preserves its unit condition by
`peeledDenominator_decimalUnit`; the factored shell of `R` makes `N'` a decimal unit through
`decimalUnit_of_factoredShell`. Sign changes preserve every finite valuation. Neither centered
reset nor any normalization can therefore enter an excluded nonunit case.

## Master Delta

Every surviving consecutive multi-shell transition now meets the `m≥3` premise used by
`peeledNumerator_forces_lastDigit`. The modulo-`100` carrier law has no exceptional branch.
The compatible period-two unit cycle still survives, however. Closure still requires a higher
decimal suffix invariant for generalized residuals. [`MM-S20`](../SALVAGE.md#mm-s20-singleton-carrier-classification)
subsequently classifies singleton-current transitions and proves the long multi-to-singleton
branch sharp for unrestricted decimal-unit carriers; encoded reachability remains open.

## Verification

The narrow module build, Lean language-server diagnostics, namespace lint, and selected
transitive axiom snapshots pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterDepth.lean`](../MatrixMortality/DecimalSetterDepth.lean)
- [`m53-decimal-recursive-carrier-2026-08-30.md`](m53-decimal-recursive-carrier-2026-08-30.md)
- [`SALVAGE.md`](../SALVAGE.md#mm-s18-length-two-carrier-extinction)
