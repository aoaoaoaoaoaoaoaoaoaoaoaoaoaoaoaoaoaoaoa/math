# M₄(3) phase-zero right-`c` `bb`-body audit

**Date:** 31 August 2026

**Status:** the shortest residual body `bb` is excluded in the `0|2|1` `b|b|c` family

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** remove the shortest body left after the S21 parity rectangle and S22 all-`c` ray

## Verdict

The body `bb` has encoded length `10`, scale coordinate `S=3^10=59049`, and code coordinate
`C=49532`. Lean proves the exact identity

```text
H(59049,49532,x,y,z) = 16Q(x,y,z)+8
```

for an explicit integral trilinear polynomial `Q`. The primitive core is therefore nonzero for
all natural waits. The determinant is a fixed nonzero rational multiple of this core, so `bb`
cannot close the shortest bridge.

## Proof Boundary

`ParabolicBlade.bZeroBDefectCOneCodeCore_bb_factor` evaluates the actual tag encoding rather
than assuming its coordinates. `ParabolicBlade.bridge_bZero_bTwo_cOne_det_ne_zero_of_bb`
transfers the integral congruence through the exact rational determinant identity. The proof
does not sample waits, alter the fixed boundaries, or substitute adjugate-transpose exterior
dynamics for the primal bridge matrices.

## Scope

The result treats exactly three atoms at `β=3`, orientation `0|2|1`, letters `b|b|c`, and the
single body `bb`. Longer all-`b` bodies, mixed even/even bodies, other shortest families,
longer defect runs, and nontrivial safe contexts remain open. Six shortest letter families
remain, but no length-two body survives in this body's parity rectangle.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean
`4.33.1`. The audited public theorems have their complete transitive axiom sets recorded in
`verification/axioms.txt`. No proof aperture, external declaration, or linter suppression was
added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
