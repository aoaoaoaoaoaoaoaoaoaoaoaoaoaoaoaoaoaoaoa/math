# M₄(3) phase-zero right-`c` `x=211` SFFT audit

**Date:** 31 August 2026

**Status:** exact positive divisor reduction and elimination resultants are formalized

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** expose the arithmetic structure of the first-`b`-after-one-`c` chamber

## Verdict

At outer wait `x=211`, Lean collects the primitive core as

```text
H=−32Nyz+8My+12Cz+3K.
```

For `U=8Ny−3C` and `V=4Nz−M`, every zero obeys

```text
UV=67908593862DW=2·3^14·31·229·D·W.
```

The two reconstruction divisibilities, fixed residue classes modulo `3`, and four exact
resultants eliminating the complement coordinate between `U`, `V`, and `W` are also proved. On
every physical `cb` cylinder, `N,M,C,K,W` are positive; at a zero, `U,V` are positive.

## Proof Boundary

The normal form, divisor identity, fixed-content factorization, congruences, and resultants are
exact polynomial identities. Positivity is proved on the full rational `cb` density interval,
then specialized to physical tag bodies through exact scale and complement formulas.

No divisor allocation is enumerated, and no theorem in this module claims that the `x=211`
slice is empty.

## Scope

The reduction concerns the outer-wait-`211` slice of bodies beginning `cb`. Its role is to turn
a bilinear zero equation into a positive factorization with controlled reconstruction and gcd
data. Other outer waits and other first-`b` positions are outside its scope.

## Validation

`MatrixMortality.ParabolicFirstBOneSFFT` builds without warnings under Lean `4.33.1`. The
public theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof
aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicFirstBOneSFFT.lean`](../MatrixMortality/ParabolicFirstBOneSFFT.lean)
