# M₄(3) minimal all-`b` bad-run audit

**Date:** 30 August 2026

**Status:** both orientations of the shortest bad defect skeleton are excluded for all-`b` atoms

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** lift the first modulo-three survivor from `M4-S06` to an exact rational obstruction

## Verdict

The shortest bad run consists of one residue-two atom between opposite safe phases. With letter
`b` throughout, the two exact middles are

```text
B₀=B_b(3z) B_b(3x+2) B_b(3y+1),
B₁=B_b(3z+1) B_b(3x+2) B_b(3y).
```

Lean proves

```text
det Kρ(B₀) = (81/2) ρ y P₀(ρ,x,z),
det Kρ(B₁) = −243 ρ z P₁(ρ,x,y).
```

After collecting by the wait monomials, every coefficient of `P₀` is strictly positive for
`ρ≥1`; every coefficient of `P₁` is strictly positive for `ρ≥9`. Hence the first determinant is
positive when `y>0`, and the second is negative when `z>0`. Those inequalities are exactly the
regular cases: `y=0` or `z=0` would place the exceptional singular atom `b(1)` at an endpoint.
At `ρ=3^β`, both orientations are therefore nonzero for every `β≥2`, including the source scale
`β=3`.

## Proof Boundary

`ParabolicBlade.bAtom_three_mul_matrix`,
`ParabolicBlade.bAtom_three_mul_add_one_matrix`, and
`ParabolicBlade.bAtom_three_mul_add_two_matrix` give the exact three residue classes of `b` atoms.
The two determinant theorems substitute those matrices into the checked bridge definition and
normalize the resulting rational polynomial. The nonzero corollaries group the final factors by
`xz,x,z,1` and `xy,x,y,1`. Elementary inequalities `ρ≤ρ²≤ρ³≤ρ⁴` for `ρ≥1`, and
`9ρ≤ρ²`, `9ρ²≤ρ³`, `9ρ³≤ρ⁴` for `ρ≥9`, prove every grouped coefficient positive.

No finite search, floating-point calculation, or unverified polynomial certificate enters the
result.

## Scope

This is an exact three-atom theorem. It allows arbitrary nonnegative waits and every `β≥2`, but
requires letter `b` at the two safe endpoints and at the defect. It does not exclude a `c`
defect, a `c` endpoint, a run of length `1+4k` with `k>0`, or a longer safe endpoint context.

The next attack should preserve the sign proof while generalizing in that order. In particular,
the protected-plane identity for four defects is not by itself an exact rational four-cycle;
the needed lift must factor the bridge determinant or transported valuation uniformly in `k`.

## Validation

The module target `MatrixMortality.ParabolicDefect` builds without warnings under Lean `4.33.1`.
The four public determinant theorems have axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefect.lean`](../MatrixMortality/ParabolicDefect.lean)
