# M₄(3) phase-zero left-`c` defect audit

**Date:** 30 August 2026

**Status:** the shortest `0|2|1` bad run with letters `c|c|b` is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** remove one of the six shortest survivors containing a `c` defect

## Verdict

Let `L` and `M` be the lower code and scale of a nonempty body. Lean proves

```text
det bridge(27, c(3z)c(3x+2)b(3y+1)) = 243y/16 · P(L,M,x,z),
```

where

```text
P = 864(M−3)(1805L+486M−3263)xz
  + 864(1805L+3263M−11594)x
  + (21400527LM−59523021L+13711802M²−102411627M+179150103)z
  − 3(19537767L−34180949M+80295864).
```

The native inequalities `27<M` and `0≤L<M` make all four coefficients strictly positive.
Regularity supplies `y>0`, so the determinant cannot vanish.

## Transposed Handoff

The same module now owns the exact integral eight-coefficient core of the immediate
`c(3z)b(3x+2)c(3y+1)` target. On the all-`c` code ray `L=M−2`, it factors as

```text
−(8(M−3)y−(M−27))
 · (304704(M−3)xz+634176x−66255239(M−3)z−138564168).
```

Lean proves this core nonzero for `M>27` and natural waits: the first factor changes sign between
`y=0` and `y=1`, while the second has its unique `x` root in `(218,219)` when `z=0` and in
`(217,218)` when `z>0`. Away from `L=M−2`, the eight coefficients have mixed signs; the
coefficientwise proof used for `c|c|b` does not extend. The remaining target is therefore the
actual non-all-`c` digit cylinders, not another raw determinant expansion.

## Scope

The exclusion treats exactly three atoms at deletion width three, with a residue-zero `c`
endpoint, a residue-two `c` defect, and a regular residue-one `b` endpoint. It does not cover the
opposite orientation, another `c` endpoint, a longer defect run, or nontrivial safe contexts.

## Validation

The target `MatrixMortality.ParabolicMixedEndpoint` builds without warnings under Lean `4.33.1`.
No proof aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicMixedEndpoint.lean`](../MatrixMortality/ParabolicMixedEndpoint.lean)
