# M₄(3) minimal triple-b defect audit

**Date:** 30 August 2026

**Status:** both all-`b` shortest three-defect runs between equal phases are excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** establish the characteristic-zero base case for the second bad residue class

## Verdict

The protected-plane zero table has a second minimal bad incidence: three consecutive
residue-two atoms between equal safe phases. At deletion width three, the all-`b` phase-zero
word is

```text
b(3z) b(3a+2) b(3b+2) b(3c+2) b(3y).
```

Lean computes its bridge determinant as `6561/32` times `tripleBDefectZeroCore a b c y z`.
The core is multilinear in `a,b,c,y,z`; all 32 coefficients are positive integers. It is
strictly positive for every nonnegative choice of waits, so the determinant never vanishes.

The phase-one word is

```text
b(3z+1) b(3a+2) b(3b+2) b(3c+2) b(3y+1).
```

Its determinant is `−2187yz/4` times `tripleBDefectOneCore a b c`. The core has eight positive
integer coefficients. Under the regularity conditions `y,z>0`, the determinant is strictly
negative.

## Proof Boundary

`ParabolicBlade.bridge_bZero_bTwo_bTwo_bTwo_bZero_det` and
`ParabolicBlade.bridge_bOne_bTwo_bTwo_bTwo_bOne_det` substitute the exact width-three atom
matrices into the checked bridge and normalize their determinants. Their nonzero corollaries use
only nonnegativity of natural waits, positivity of the displayed coefficients, and the two
phase-one regularity assumptions. No floating-point estimate, sampled wait range, or external
polynomial certificate enters the result.

## Scope

The result treats exactly three consecutive defects, equal safe phases, deletion width `β=3`,
and letter `b` at all five atoms. It does not cover a body-dependent `c` atom, a run of length
`3+4k`, or a nontrivial safe context. The phase-one conditions exclude singular `b(1)` endpoints.

Together with `M4-S09`, the theorem gives all-`b` base exclusions for both bad residue classes.
It does not prove that the characteristic-zero bridge inherits the protected-plane four-cycle,
and it does not decide `M₄(3)`.

## Validation

`MatrixMortality.ParabolicLongDefect` builds without warnings under Lean `4.33.1`. The default
namespace linter and fresh Lean LSP diagnostics are clean. Each of the four publication theorems
has axiom set exactly `[propext, Classical.choice, Quot.sound]`. No proof aperture, external
declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicLongDefect.lean`](../MatrixMortality/ParabolicLongDefect.lean)
