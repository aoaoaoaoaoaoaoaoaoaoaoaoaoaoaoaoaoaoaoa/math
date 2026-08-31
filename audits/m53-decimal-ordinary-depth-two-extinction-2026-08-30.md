# Decimal Setter Ordinary Depth-Two Extinction Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every ordinary-reset false-pole branch after two completed transfers is empty

This audit closes the three resonant families isolated by the ordinary depth-two shell forest.
It does not prove arbitrary-depth projective avoidance or settle `M₅(3)`.

## A-To-B Phase Exhaustion

The shell forest leaves all-`c` middle blocks of upper length `β+1` or `β+2` before a singleton
target. Encode a rule phase by `true` and an erasure phase by `false`. Lean proves the exact
exhaustion

```text
phases = D_c^n,       or       phases = D_c^i R_c s.
```

For an all-deletion word, upper and lower spellings have equal positive length and the normalized
lower code is in `(0,7/9)`. At `ρ≥1000`, this gives lower J-weight `0<v<1/200`. Every encoded
upper coefficient satisfies `u>4/5`, so the middle image of every ordinary first image is above
`3/4`. A singleton target has the same small lower bound and its pole is below `1/100`.

For a rule-bearing word, choose the first displayed `R_c`. Every suffix role contributes at least
one lower digit. The compiler body begins in `b`, has length at least `β−1`, and its binary
encoding has length at least `2β`. Consequently the middle lower spelling exceeds its upper
length by at least `2β+2`. It begins in `7` if `i>0` and in `55` if `i=0`, so

```text
normalized lower ≥ 55ρ²,       v > 265ρ.
```

A `c`-leading multi-role source has `0<t<97/100` and maps below zero. A `b`-leading source lies
strictly above `1+1/(2μ)` and maps above one. Every singleton pole lies in `(0,1)`. The
declarations `allC_cLeading_avoids_singletonPole` and
`allC_bLeading_avoids_singletonPole` therefore kill both long shell lengths at once.

## B-To-A Factorization

The remaining B/A shell word has `β` all-`c` source roles followed by singleton `D_b`. Its first
image depends only on the common upper spelling:

```text
t₁=(50ρ²+2ρ−7)/(ρ(52ρ−7)).
```

Substitution of the exact `D_b` coefficients gives

```text
t₂−1=(10ρ−1)(502ρ−7)/(20(52ρ−7)(50ρ²+2ρ−7)).
```

Every factor is positive for `ρ≥1000`; hence `t₂>1`. Every encoded target has positive upper
and lower coefficients, so its pole lies strictly in `(0,1)`. Lean checks the encoded statement
as `encodedSingleB_after_repeatedC_avoids_encodedPole`.

## Assembly And Scope

[`MM-S14`](../SALVAGE.md#mm-s14-ordinary-depth-two-shell-forest) proves that A/A, A/B, B/A, and
B/B are the complete ordinary shell table. [`MM-S15`](../SALVAGE.md#mm-s15-ordinary-a-to-a-length-two-extinction)
kills A/A; B/B is empty in the shell theorem; the two arguments above kill A/B and B/A.
`compilerBody_resonanceEnvelope` formally supplies `β≥3`, the body-length bound, and the leading
`b` for every compiled source. Thus the ordinary reset has no false pole through depth two.

The distinguished reset has a nonunit initial discrepancy and is not covered. Nor do the
two-transfer identities constrain an ordinary orbit after a third transfer. These are the live
frontiers.

## Verification

The module and root builds, namespace lint, Lean language-server diagnostics, and transitive
axiom snapshots pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterResonance.lean`](../MatrixMortality/DecimalSetterResonance.lean)
- [`m53-decimal-depth-two-shell-forest-2026-08-30.md`](m53-decimal-depth-two-shell-forest-2026-08-30.md)
- [`m53-decimal-length-two-chamber-2026-08-30.md`](m53-decimal-length-two-chamber-2026-08-30.md)
- [`SALVAGE.md`](../SALVAGE.md#mm-s16-complete-ordinary-depth-two-extinction)
