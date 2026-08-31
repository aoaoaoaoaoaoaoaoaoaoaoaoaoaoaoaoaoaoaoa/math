# M₄(3) phase-zero right-`c` complement-SFFT audit

**Date:** 31 August 2026

**Status:** the mixed complement core reduces exactly to a finite divisor equation

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** expose an arithmetic engine for the complement state surviving `M4-S25`

## Verdict

At `C=S−1−D`, write the primitive core as

```text
H(S,S−1−D,x,y,z) = ayz + by + cz + d,
```

where `a,b,c,d` are explicit integral polynomials in `S,D,x`. Lean proves

```text
bc−ad = −306110016 D (48x−3029)
        (1096376045D + 2022264Sx − 3287358654S − 224696x + 366706454)
```

and the SFFT identity

```text
(ay+c)(az+b) = aH + (bc−ad).
```

Thus a zero makes two affine integer factors multiply to an explicit product of three linear
factors. For fixed `S,D,x`, only finitely many divisors can occur. The same module proves the
sharp global tag bound `242D≤39(S−1)`, with equality approached along the all-`b` ray.

## Proof Boundary

`ParabolicBlade.bZeroBDefectCOneCodeCore_complement_collect` computes the four coefficients.
`bZeroBDefectCOneComplement_discriminant` and `bZeroBDefectCOneComplement_sfft` are polynomial
identities over the integers. `tagComplementCode_global_bound` is an induction over physical
tag words using the exact append recurrences. No numerical search is promoted into the claim.

## Scope

The identities apply to the primitive core of the `0|2|1` `b|b|c` family for arbitrary
integral coordinates. They provide a finite decision procedure at fixed body coordinates but
do not yet prove a uniform no-go for every mixed body.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
