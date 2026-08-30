# M₄(3) residue-one left `c`-endpoint audit

**Date:** 30 August 2026

**Status:** the `1|2|0` shortest bad run is excluded with a `c` left endpoint and `b` middle and
right atoms

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** close the residue-one left endpoint left open by `M4-S12`

## Verdict

At deletion width three, write `L` and `M` for the lower code and scale of an arbitrary nonempty
body. Lean collects the bridge determinant of

```text
c(3z+1) b(3x+2) b(3y)
```

as

```text
314928αxyz + 39366βxy + 39366αxz + (19683/4)βx
  + 2187γyz + (2187/8)δy + (2187/4)εz + (2187/32)η,
```

where

```text
α = −60243L + 202676M − 547785,
β = 28630152L + 52341077M − 178357047,
γ = −310354809L + 1148871068M − 3136258395,
δ = 146643059556L + 295516990211M − 991890425661,
ε = −92189577L + 354833788M − 972311787,
η = 43449428727L + 91132916596M − 304097945043.
```

The native bounds `27<M` and `0≤L<M` make all six quantities strictly positive. The determinant
is therefore positive for every triple of nonnegative waits. Unlike the cases with a residue-one
`b` endpoint, no wait must be excluded: the residue-one `c` atom is invertible for every
nonempty body, and the residue-zero `b` endpoint is always regular.

## Proof Boundary

`ParabolicBlade.bridge_cOne_bTwo_bZero_det` substitutes the exact residue-one `c`, residue-two
`b`, and residue-zero `b` matrices into the checked bridge and normalizes the determinant.
`ParabolicBlade.bridge_cOne_bTwo_bZero_det_ne_zero` proves the six coefficient inequalities and
closes the sum by positivity. No body enumeration, floating-point estimate, or unverified
polynomial certificate enters the result.

## Scope

The theorem treats exactly three atoms at `β=3`, with a `b` defect, a residue-one `c` left
endpoint, and a residue-zero `b` right endpoint. The transposed residue-one right endpoint,
simultaneous `c` defect and endpoint atoms, longer defect runs, and nontrivial safe contexts
remain outside the claim.

## Validation

The target `MatrixMortality.ParabolicDefect` builds without warnings under Lean `4.33.1`. Both
public theorems have axiom set exactly `[propext, Classical.choice, Quot.sound]`. No proof
aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefect.lean`](../MatrixMortality/ParabolicDefect.lean)
