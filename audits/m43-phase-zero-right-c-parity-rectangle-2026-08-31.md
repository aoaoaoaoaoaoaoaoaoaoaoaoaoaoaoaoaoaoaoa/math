# M₄(3) phase-zero right-`c` parity-rectangle audit

**Date:** 31 August 2026

**Status:** three body-parity classes are excluded in the `0|2|1` `b|b|c` family

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** contract the even-length residue left by `M4-S19` and adjudicate further 2-adic cuts

## Verdict

For an arbitrary body, set

```text
S = 3^length(tagEncode₃(body)),
C = ternaryCode(tagEncode₃(body)).
```

The exact determinant from `M4-S19` is `−2187/64 · H(S,C,x,y,z)`. If the body length is even
and its `b` count is odd, the tag encoding gives `S=8s+1` and `C=2c+1`. Lean checks

```text
H(8s+1,2c+1,x,y,z) = 8U(s,c,x,y,z)+4,
```

so the determinant cannot vanish at any natural wait triple. `M4-S19` independently excludes
every odd-length body. A zero in this shortest family therefore requires both even body length
and even `b` count.

The surviving rectangle resists every uniform fixed 2-power congruence. For the lawful body
`bbcc`, Lean evaluates the coordinates to `S=531441`, `C=445796` and proves

```text
H(S,C,x,y,z) = 32 P(x,y,z),
P(0,0,z) = 4981923137668815z + 461209693766445.
```

The coefficient of `z` is odd and is therefore a unit modulo every power of two. At every
fixed 2-adic precision there is a natural residue representative `z` for which the core is zero
modulo that precision. This does not produce an exact integer zero; it closes only the proposed
higher-fixed-modulus route.

## Proof Boundary

`ParabolicBlade.bridge_bZero_bTwo_cOne_det_ne_zero_of_even_body_odd_b_count` derives the encoded
length and code residues from the checked tag recurrences and uses an explicit integral
factorization. `ParabolicBlade.bZeroBDefectCOneCodeCore_bbcc_factor` computes the residual
body's exact primitive core. Neither theorem samples waits, changes the fixed boundaries, nor
substitutes adjugate-transpose exterior dynamics for the primal bridge matrices.

## Scope

The exclusion treats exactly three atoms at `β=3`, orientation `0|2|1`, and letters `b|b|c`.
It leaves the even-length, even-`b` bodies, every other shortest family, longer defect runs, and
nontrivial safe contexts open. Six shortest families remain.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean
`4.33.1`. The audited public theorems have their complete transitive axiom sets recorded in
`verification/axioms.txt`. No proof aperture, external declaration, or linter suppression was
added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
