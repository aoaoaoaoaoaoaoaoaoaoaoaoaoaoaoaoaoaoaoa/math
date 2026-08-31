# Global One-`D_b` Raw-Head Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** no one-`D_b` all-erasure block carries a lawful two-`c` raw head into another
multi-role pole, regardless of the `D_b` position

## Exact Data

Let `a` and `t` count the `D_c` roles before and after the sole `D_b`, and put `n=a+t+1`.
The punctuated upper codes satisfy

```text
P_b − P_c = D(a)·10^(t+β+2),       D(a) ≡ 2 (mod 5).       (1)
```

At the exceptional raw head, the all-`D_c` residual has the normal form

```text
45R_c = 10^n·5C + 10^(2β)B,        C ≡ 2, B ≡ 1 (mod 5).  (2)
```

The head and gap coefficients are both `2` modulo `5`. Hence the third term in `45R_b` is
`10^(t+β+2)·5Q`, where `Q≡2 (mod 5)`.

## Depth Exhaustion

After the regular and early cuts of `MM-S45`, only `a>β` remains. The three term depths are

```text
n+1,  2β,  t+β+3.
```

If `a=β+1`, the first and third depths coincide; if `a≥β+2`, the third is shallower. Comparing
`t+3` with `β` supplies the other strict order or equality. A unique shallow term has a unit
coefficient. The first/third resonance has coefficient `C+Q≡4`; the second/third resonance has
coefficient `2B+Q≡4`; the common corner has coefficient `C+2B+Q≡1`. None can acquire the target
depth `n+β`.

Combining the exceptional-late extinction with `MM-S45` proves the unrestricted physical
one-marker theorem.

## Scope

The result covers exactly one `D_b`, otherwise `D_c`, no rule roles, the distinguished lawful
two-`c` raw head, and a following multi-role pole. Multiple `D_b` roles, rule-bearing blocks,
singleton targets, and later generalized carriers remain open.

## Verification

`MatrixMortality/DecimalSetterFiveDepth.lean` checks the coefficient normal form and all six
depth branches. `MatrixMortality/DecimalSetterPositioned.lean` checks the exact physical suffix
factor, its unit coefficient, the exceptional specialization, and the all-position corollary.
Narrow and root builds, Lean language-server diagnostics, namespace lint, and selected
transitive axiom snapshots pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterFiveDepth.lean`](../MatrixMortality/DecimalSetterFiveDepth.lean)
- [`DecimalSetterPositioned.lean`](../MatrixMortality/DecimalSetterPositioned.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s47-global-one-d_b-raw-head-extinction)
