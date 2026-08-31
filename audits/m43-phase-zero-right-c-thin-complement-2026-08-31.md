# M₄(3) phase-zero right-`c` thin-complement audit

**Date:** 31 August 2026

**Status:** every positive complement thinner than `1/2160000` of the code scale is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** kill the thin end of the mixed complement state surviving `M4-S25`

## Verdict

At `C=S−1−D`, Lean checks

```text
H(S,S−1−D,x,y,z) = (72Sy−9S−8y+9)P(x,z) + D J(x,y,z),
```

where `J` has positive coefficients. If `D>0` and `2160000D≤S−1`, this core is nonzero
for every natural `x,y,z`. Hence a physical body satisfying

```text
0<D  and  2160000D<S
```

cannot close the `0|2|1` bridge with letters `b|b|c`.

## Proof Boundary

The core is affine in `x`. At `y>0`, exact coefficient comparisons make its value negative at
`x=214` and positive at `x=215`; the comparison uses only `22000D<S`. At `y=0`, the signs
reverse, and `1080000D<S−1` controls the positive complement term at `x=215`. Any rational
root therefore lies strictly between 214 and 215. The physical theorem derives the closed
rational inequality from the strict natural inequality and transfers integral core
nonvanishing through the exact determinant identity.

No bounded body search, floating-point inequality, or unproved prefix classification enters
the theorem.

## Scope

The theorem applies only to the deletion-width-three, three-atom, phase-zero right-`c` family
and physical bodies in the stated complement cone. It does not classify the denser complement
region, longer defect runs, or other atom-letter families.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
