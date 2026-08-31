# M₄(3) phase-zero right-`c` all-`c` ray audit

**Date:** 31 August 2026

**Status:** every nonempty all-`c` body is excluded in the `0|2|1` `b|b|c` family

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** begin the archimedean attack on the even/even residue left by `M4-S21`

## Verdict

For an all-`c` body the tag encoding gives `C=S−1`. Lean checks the exact factorization

```text
H(S,S−1,x,y,z)
  = (72Sy−9S−8y+9)
    (119911680xz+11209824x−25766986436z−2408152393).
```

Nonempty bodies have `S>1`. The first factor is strictly negative at `y=0`. For `y≥1`, write
it as `(72S−8)(y−1)+63S+1`, which is strictly positive. For the second factor, its positive
`x` coefficient obeys the exact endpoint inequalities

```text
25766986436z+2408152393 − 214(119911680z+11209824)
  = 105886916z+9250057 > 0,

215(119911680z+11209824) − (25766986436z+2408152393)
  = 14024764z+1959767 > 0.
```

Any natural root would satisfy `214<x<215`. Hence the determinant is nonzero for every
nonempty body `c^k` and every natural wait triple.

## Proof Boundary

`ParabolicBlade.bZeroBDefectCOneCodeCore_all_c_factor` proves the polynomial identity over an
arbitrary commutative ring. `ParabolicBlade.bridge_bZero_bTwo_cOne_det_ne_zero_of_c_run`
specializes the checked tag code and proves both strict inequalities over the rationals. The
proof does not sample waits, alter the fixed boundaries, or substitute adjugate-transpose
exterior dynamics for the primal bridge matrices.

## Scope

The result treats exactly three atoms at `β=3`, orientation `0|2|1`, letters `b|b|c`, and the
entire nonempty all-`c` body ray. Bodies containing `b`, other shortest families, longer defect
runs, and nontrivial safe contexts remain open. Six shortest letter families remain, but the
even/even residue no longer contains `cc` or any longer all-`c` body.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean
`4.33.1`. The audited public theorems have their complete transitive axiom sets recorded in
`verification/axioms.txt`. No proof aperture, external declaration, or linter suppression was
added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
