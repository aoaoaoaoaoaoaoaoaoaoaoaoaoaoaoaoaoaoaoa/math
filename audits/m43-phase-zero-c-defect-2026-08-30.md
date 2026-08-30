# M₄(3) phase-zero `c`-defect audit

**Date:** 30 August 2026

**Status:** the `0|2|1` shortest bad run is excluded with a `c` defect and `b` endpoints

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** extend `M4-S09` from an all-`b` defect to the body-dependent `c` defect

## Verdict

At deletion width three, let `L` and `M` be the native lower code and scale of an arbitrary
nonempty body. Lean computes the bridge determinant of

```text
b(3z) c(3x+2) b(3y+1)
```

as `729y/16` times

```text
Cₓ𝓏 xz + Cₓ x + C𝓏 z + C₁,
```

where

```text
Cₓ𝓏 = 1338308352(M−3),
Cₓ  = 864(48735L+96151M−337188),
C𝓏  = 8(−40006914L+6584307989M−19211051421),
C₁  = 1617993993L+3268306175M−11182600422.
```

The exact code bounds `27<M` and `0≤L<M` make all four coefficients strictly positive.
Regularity forces `y>0`, because `y=0` is the exceptional singular endpoint `b(1)`. The bridge
determinant is therefore positive for every nonnegative `x,z` and every nonempty body.

## Proof Boundary

`ParabolicBlade.cAtom_three_mul_add_two_matrix` exposes the exact residue-two `c` atom.
`ParabolicBlade.bridge_bZero_cTwo_bOne_det` substitutes it and the two exact `b` residue matrices
into the checked bridge. `ParabolicBlade.bridge_bZero_cTwo_bOne_det_ne_zero` obtains the code
bounds directly from `ternaryCode_lt_pow_length` and nonemptiness of `tagEncode`, proves the four
coefficient inequalities, and concludes by positivity.

No enumeration of bodies or waits enters the theorem. The bound is specific to `β=3`; no
unverified symbolic calculation is retained as evidence.

## Scope

The theorem treats exactly three atoms, a `c` defect, `b` endpoints, and phase pattern `0|2|1`.
The opposite pattern `1|2|0` remains open. Its exact determinant has mixed coefficient signs and
reduces to a linear Diophantine relation in the body code and waits, so the present positivity
proof cannot be mirrored.

The reduction itself is now kernel-checked. Put

```text
B_y=1316002776L−442700696M−28695312,
B₀ =164500347L−55585393M−2843496.
```

Then

```text
det K₂₁₀ = −4374z(1699776(M−3)(8y+1)x−B_y y−B₀),
B_y−8B₀ = 1982448(M−3).
```

The second identity fixes the width of the corresponding rational `x` interval at
`1982448/(8·1699776)=1059/7264<1`, independently of the body. Exclusion of its sole possible
integer is the remaining digit-cylinder obligation; it is not claimed here.

Endpoint `c` atoms and runs of length `1+4k` remain subsequent generalizations.

## Validation

The target `MatrixMortality.ParabolicDefect` builds without warnings under Lean `4.33.1`. The
four public theorems have axiom set exactly `[propext, Classical.choice, Quot.sound]`. No proof
aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefect.lean`](../MatrixMortality/ParabolicDefect.lean)
