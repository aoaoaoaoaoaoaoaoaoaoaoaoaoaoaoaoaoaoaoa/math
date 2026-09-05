# Compiler-Congruence Extinction of Decimal Peeled Heads

**Date:** 2026-09-04
**Target:** M₅(3)
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the long `R_c`-rooted three-block singleton branch is empty on the
compiler image. M₅(3) remains open.

## Source Charge

Every compiler body satisfies `β>2` and `(β−1) ∣ |body|`. The prior long-head
arithmetic did not consume the second condition.

For a binary word v and a preceding bit ε, define

```text
χβ(ε; v) = |v| − (β+1) N₀₁(εv),
```

where N₀₁ counts adjacent zero-to-one transitions, including the transition
from ε to the first bit. The preceding bit is not counted in |v|. Each bit
therefore contributes one except for a one following a zero, which contributes
−β. This is a word invariant, not an invariant of arbitrary rational rays.

The upper codes `1` and `10^β1` each have charge one from an incoming one
and end in one. An upper spelling of n roles has charge n; its terminal
marker `10^β` contributes β+1. Every lower role ends in zero. From an
incoming zero, the lower charges are

```text
D_b, D_c : 1
R_b      : 2−β
R_c      : |body|+2−β.
```

All are one modulo β−1 on the compiler's body-length class. The complete
lower spelling of n roles therefore has charge n modulo β−1.

An exact shifted match

```text
upper(w) · marker = 1^a 0^s · lower(w),   s>0,
```

must satisfy `a+s ≡ β+1 (mod β−1)`. Indeed, the right prefix ends in zero,
so the incoming-bit conventions agree; taking charges cancels n from both
sides. A head of length β+2 would make β−1 divide one. No halting premise,
leading-letter hypothesis, coprimality condition, or word-length bound is used.

## Decimal Consumers

Let P be the punctuated upper decimal code, V the complete lower code, and
k the unpunctuated upper length. Exact suffix exhaustion gives

```text
P>V,   ν₂(P−V)=ν₅(P−V)=k−1,   k≥2
  ⇒ upper(w) · marker = H · lower(w),   |H|=β+2,
```

with H a decimal-unit head. The upper grammar leaves a `b`, `cb`, or `cc`
head. The `b` head ends in digit five and is not a decimal unit. Both other
heads are `1^a0^s` with s>0. The source charge thus excludes the entire
positive equal-depth raw-discrepancy language.

Two checked pole consequences follow.

1. A multi-role erasure-ended target cannot hit after one multi-digit block
   above `R_c`. Its equation is `T(P−V)=GV_target Aμ`, where A=10^k and T
   has shell `(1,1)`. Positivity and the unit factors force precisely the
   excluded discrepancy shell.
2. The entire long three-source-block singleton branch above `R_c` is empty.
   `MM-S94` forces that same exhausted suffix in the intervening block. This
   closes the `cc` branch left by `MM-S103`, uniformly over both singleton
   targets, without further gap-factor analysis.

The refined three-block singleton classifier leaves only a deep root with a
two-`c` intervener and a long current, or `R_c` with an all-`c` current of
role length 2 through β+2. The generalized suffix theorem now owns the
arithmetic formerly embedded in the three-block suffix proof.

## Scope Checks

The body congruence is essential. At β=3 and body `bbb`, the word
`R_c D_b D_b R_b D_b D_b` satisfies

```text
upper(w) · marker = 11000 · lower(w).
```

Direct binary-word concatenation checks this specimen. Here |body|=3 is not
divisible by β−1=2; it is not a compiler-image counterexample.

After several square resets, a rational numerator is a product residual,
not a binary word. Neither theorem identifies that residual with an encoded
head. Applying the charge inductively without an ancestry theorem would be
invalid. In particular, this does not contradict the existing finite-residue
or first-cylinder no-gos: it removes a literal word language they do not retain.

The global shortening argument remains unproved. There is no arbitrary-depth
bound, no counterexample to the decimal construction, and no M₅(3) endpoint
here. Primitive-recursive emission of the decimal integer family also remains
a separate endpoint obligation.

## Verification

`scripts/check.sh` passes: the 9301-job Lean build, whole-library default
linters, reviewed transitive axiom snapshot, proof-aperture scans, exact symbolic
checks, and publication reproduction. The ten new audited declarations depend
only on subsets of `propext`, `Classical.choice`, and `Quot.sound`. Both new
modules also returned no language-server diagnostics. The symbolic checks are
auxiliary; Lean proves the new charge and every stated pole consequence.

## Artifacts

- `MatrixMortality/NearyPulseCharge.lean`: source charge and shifted-match obstruction.
- `MatrixMortality/DecimalSetterPulseCharge.lean`: raw-peel extinction, pole consumers,
  and the compiler-image classifier.
- `MatrixMortality/DecimalSetterCarry.lean`: equal-depth suffix extraction.
- `MM-S108` in `SALVAGE.md`: the durable result boundary.
