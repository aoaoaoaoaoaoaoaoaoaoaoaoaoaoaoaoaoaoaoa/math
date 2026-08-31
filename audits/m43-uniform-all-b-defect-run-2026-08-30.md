# M₄(3) uniform all-`b` defect-run audit

**Date:** 30 August 2026

**Status:** every regular all-`b` safe/defect/safe bridge is excluded for an arbitrary finite
residue-two run

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace the finite one- and three-defect coefficient expansions by one unbounded
characteristic-zero transport theorem

## Verdict

At deletion width three, encode a safe `b` endpoint of phase `ε` and wait `j` by

```text
Bε(j) = b(3j)       if ε=0,
Bε(j) = b(3j+1)     if ε=1,
```

and a residue-two defect by `D(j)=b(3j+2)`. For arbitrary phases `ε,δ`, endpoint waits `z,y`,
and every finite list `w`, Lean proves

```text
det bridge(27, Bε(z) · D(w₀) ··· D(wₙ₋₁) · Bδ(y)) ≠ 0
```

provided both endpoints are regular. Regularity excludes exactly `B₁(0)=b(1)`; residue-zero
endpoints and positive-wait residue-one endpoints require no further restriction. The theorem
does not require the run to be nonempty or odd. It therefore covers both bad-skeleton lengths
`1+4k` and `3+4k`, and more.

## Cone Certificate

Let `S=diag(1,−1,−1)`. The adjugate-transpose action of `D(j)` is, after conjugation and one
global minus sign, the matrix

```text
H(j) = [ 0,          4617+5832j, 745281/8  ]
       [ 3029/2−24j, 3865+4896j, 312823/4  ]
       [ 0,          8262+11664j,744309/4  ].
```

For every rational `j≥0`, this action preserves

```text
K = {(x,y,z) : 0<x, x≤2y, 7y≤6x, x≤z}.
```

The proof clears the four defining inequalities directly. The apparently negative coefficient
`3029/2−24j` is absorbed by the cone walls; no entrywise-positivity claim is used. Both regular
right endpoints map into `K`. On `K`, the signed residue-zero left covector is strictly negative,
while the signed regular residue-one left covector is strictly positive. Induction through the
run yields only the scalar factor `(−1)^n`, which is nonzero.

## Proof Boundary

`ParabolicBlade.bridge_bSafe_bDefectRun_bSafe_det_ne_zero` consumes the exact residue-class atom
matrices, the adjugate product law, and the checked bridge determinant covector. All cone walls,
endpoint vectors, and endpoint covectors are proved by exact rational normalization. The run is
an ordinary Lean list and the preservation proof is structural induction; no bounded search,
floating-point estimate, or unverified symbolic certificate enters the theorem.

The result subsumes the exact one-defect nonzero corollaries in `ParabolicDefect.lean` and both
three-defect nonzero theorems formerly in `ParabolicLongDefect.lean`. The two 32-coefficient
three-defect cores and their four public theorems were deleted rather than retained beside the
uniform invariant.

## Scope

Every atom in the run and both single-atom endpoints must be `b`, and the scale is exactly
`β=3`. The theorem does not cover a `c` defect, a `c` endpoint, or a safe endpoint context with
more than one atom. Those body-dependent families remain separate characteristic-zero
incidence problems.

## Validation

The target `MatrixMortality.ParabolicLongDefect` builds without warnings under Lean `4.33.1`.
The public nonzero theorem has axiom set exactly `[propext, Classical.choice, Quot.sound]`. No
proof aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicLongDefect.lean`](../MatrixMortality/ParabolicLongDefect.lean)
