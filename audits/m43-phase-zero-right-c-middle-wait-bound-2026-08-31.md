# M₄(3) phase-zero right-`c` middle-wait audit

**Date:** 31 August 2026

**Status:** every first-`b` core zero has middle wait at most `51767`

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** make the unbounded middle-wait axis finite without a body census

## Verdict

For a body `c^j b v`, with ternary scale `S` and complement `D=S−C−1`, Lean proves

```text
242·3^jD ≤ 39(S−1).
```

If its phase-zero right-`c` primitive core vanishes, then

```text
y<51768,
```

equivalently `y≤51767` for the natural middle wait.

## Proof Boundary

The sharp upper cylinder retains the constant gap discarded by the earlier open density bound.
The core proof treats the exact regimes `j=0`, `j=1`, `j=2`, and `j≥3`. In each regime,
explicit endpoint identities and monotonicity in the outer and middle waits force a strict sign
once `y≥51768`. All comparisons are rational or natural arithmetic checked by Lean.

No body-length cutoff, floating-point estimate, or enumerated wait sample enters the theorem.

## Scope

The theorem applies to every physical tag body containing `b`, because each has a unique
first-`b` decomposition. It bounds only the middle wait in the primitive `b | b | c` core; it
does not assert nonvanishing for any point below the cutoff.

## Validation

`MatrixMortality.ParabolicWaitBounds` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicWaitBounds.lean`](../MatrixMortality/ParabolicWaitBounds.lean)
