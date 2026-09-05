# Decimal Code-Difference Valuation Gap

**Date:** 2026-09-04
**Target:** M₅(3)
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the exceptional pure-erasure three-source branch before `D_b`
is empty. M₅(3) remains open.

## Word Bound

Encode binary words in radix ten by `1↦5`, `0↦7`. For arbitrary words u,v,

```text
ν₅(code(u)−code(v)) ≤ ν₂(code(u)−code(v)) + 2.       (1)
```

First, no nonempty code is divisible by 125. Its residue modulo 25 belongs
to `{0,2,5,7}`. A final seven prevents divisibility by five. A final five gives
`10N+5`; divisibility by 125 would require `N≡12 (mod 25)`, outside that set.

Now remove equal final digits from u and v. Each removal divides their
difference by ten, reducing both valuations by one. At the first unequal
digits, the difference is `10N±2`, hence a five-adic unit; its two-adic valuation
is nonnegative because it is an integer. If one word ends first, the remainder
is a signed nonempty code and has five-adic valuation at most two. These cases
prove (1). The equal-word case also satisfies it under the convention `ν_p(0)=0`.

The bound is sharp even with both words nonempty: `757−7=750` has
`(ν₂,ν₅)=(1,3)`. This argument uses neither Neary grammar nor the compiler's
body-length congruence.

## Pole Consumer

Consider target `D_b`, current `D_c^(β+2)`, an arbitrary intervening role word,
and root `R_c`. Let k be the intervening upper length and δ its punctuated
upper code minus its lower code. The existing exact coefficient calculation gives

```text
β≥4:  (ν₂δ,ν₅δ)=(k−4,k−1),
β=3:  (ν₂δ,ν₅δ)=(k−6,k−1).
```

The required excess is three or five, contradicting (1). Thus no such pole
exists for any `β≥3`, body, or intervening word. The previous short-intervener
exclusions are subsumed by this all-length statement.

## Remaining Boundary

Other short all-`c` currents and the deep-root branch remain. After further
resets, a rational numerator need not be a difference of code words. Applying
(1) there without reconstructing word ancestry would be invalid. There is no
arbitrary-depth converse or M₅(3) endpoint in this result.

## Verification

`scripts/check.sh` passes: the 9303-job Lean build, whole-library default
linters, reviewed transitive axiom snapshot, proof-aperture scans, exact
auxiliary audits, and publication reproduction. Both new audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The new module and both pulse-charge modules also return zero LSP diagnostics.

`MatrixMortality/DecimalSetterCodeShell.lean` owns (1) and its pole consumer.
It imports the previously separate `DecimalSetterThreeBlockAllEraseCurrent.lean`
coefficient calculation into the root build. `MM-S109` records the exact scope.
