# M₄(3) phase-zero double-`c` parity cylinder audit

**Date:** 31 August 2026

**Status:** the odd-length, odd-`b` body cylinder of the `0|2|1` `b|c|c` family is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** cut the opposite placement left open by `M4-S17`

## Verdict

For an arbitrary body, set

```text
S = 3^length(tagEncode₃(body)),
C = ternaryCode(tagEncode₃(body)).
```

Lean proves

```text
det bridge(27, b(3z)c(3x+2)c(3y+1))
  = 2187/1024 · G(S,C,x,y,z),
```

where `G` is an integral trilinear polynomial. Each `b` tag has length five and odd ternary code;
each `c` tag has length one and even ternary code. Lean derives

```text
length(tagEncode₃(body)) mod 2 = length(body) mod 2,
C mod 2 = count(body,b) mod 2.
```

For odd body length and odd `b` count, write `S=4s+3` and `C=2c+1`. The exact checked identity

```text
G(4s+3,2c+1,x,y,z) = 4Q(s,c,x,y,z)+2
```

excludes zero for all natural waits. Any zero in this family must therefore have even body
length or even `b` count.

## Proof Boundary

`ParabolicBlade.bridge_bZero_cTwo_cOne_det` substitutes the exact primal residue matrices into
the checked bridge and clears only the nonzero rational factor `2187/1024`. The parity theorem
uses an explicit integral factorization, not sampled residues or an external solver. The proof
keeps the primal atoms separate from their adjugate-transpose exterior actions.

## Scope

The result treats exactly three atoms at `β=3`, orientation `0|2|1`, letters `b|c|c`, and bodies
of odd length with an odd number of `b` letters. It does not settle the complementary parity
cylinders, another shortest family, a longer defect run, or a nontrivial safe context. Six
shortest families remain.

## Validation

The target `MatrixMortality.ParabolicDefectCylinder` builds without warnings under Lean `4.33.1`.
The two public theorems have transitive axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefectCylinder.lean`](../MatrixMortality/ParabolicDefectCylinder.lean)
