# M₄(3) phase-zero triple-`c` parity cylinder audit

**Date:** 31 August 2026

**Status:** the odd-length, odd-`b` body class of the `0|2|1` `c|c|c` family is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** extend the phase-zero parity blade across the residue-zero endpoint letter

## Verdict

For an arbitrary body, set

```text
S = 3^length(tagEncode₃(body)),
C = ternaryCode(tagEncode₃(body)).
```

Lean proves

```text
det bridge(27, c(3z)c(3x+2)c(3y+1))
  = 2187/1024 · J(S,C,x,y,z),
```

where `J` is a primitive integral trilinear polynomial. For odd body length and odd `b` count,
the tag encoding gives `S=4s+3` and `C=2c+1`. The exact checked identity

```text
J(4s+3,2c+1,x,y,z) = 4T(s,c,x,y,z)+2
```

excludes zero for all natural waits. Any zero in this family must therefore have even body
length or even `b` count.

## Proof Boundary

`ParabolicBlade.bridge_cZero_cTwo_cOne_det` substitutes the exact primal residue matrices into
the checked bridge. The nonzero theorem uses the tag-length and code-parity recurrences already
checked for `M4-S18`, followed by an explicit integral factorization. It does not use sampled
residues, an external solver, or an adjugate-transpose matrix in place of a primal atom.

## Scope

The result treats exactly three atoms at `β=3`, orientation `0|2|1`, letters `c|c|c`, and bodies
with odd length and odd `b` count. It does not settle complementary body parities, the opposite
orientation, a longer defect run, or a nontrivial safe context. Six shortest families remain.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean
`4.33.1`. The two public theorems have transitive axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
