# M₄(3) phase-zero right-`c` odd-length cylinder audit

**Date:** 31 August 2026

**Status:** odd body length is excluded in the `0|2|1` `b|b|c` family

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** cut the sole surviving one-`c` endpoint, `b`-defect family

## Verdict

For an arbitrary body, set

```text
S = 3^length(tagEncode₃(body)),
C = ternaryCode(tagEncode₃(body)).
```

Lean proves

```text
det bridge(27, b(3z)b(3x+2)c(3y+1))
  = −2187/64 · H(S,C,x,y,z),
```

where `H` is a primitive integral trilinear polynomial. Every body letter has odd encoded
length, so odd body length gives `S=4s+3`. The exact checked identity

```text
H(4s+3,C,x,y,z) = 4R(s,C,x,y,z)+2
```

excludes zero for every body code and all natural waits. Any zero in this family must therefore
have even body length.

## Proof Boundary

`ParabolicBlade.bridge_bZero_bTwo_cOne_det` substitutes the exact primal residue matrices into
the checked bridge. `ParabolicBlade.bridge_bZero_bTwo_cOne_det_ne_zero_of_odd_body` derives the
encoded-length residue and uses the explicit integral factorization. The proof neither samples
waits nor replaces the primal atoms by their adjugate-transpose exterior actions.

## Scope

The result treats exactly three atoms at `β=3`, orientation `0|2|1`, letters `b|b|c`, and odd
body length. It does not settle even-length bodies, another shortest family, a longer defect run,
or a nontrivial safe context. Six shortest families remain.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean
`4.33.1`. The two public theorems have transitive axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
