# M₄(3) opposite double-`c` endpoint audit

**Date:** 30 August 2026

**Status:** the `1|2|0` shortest bad run is excluded with a `b` defect and `c` atoms at both
endpoints

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** close the first shortest bad bridge containing two body-dependent atoms

## Verdict

At deletion width three, write

```text
D = nearySideLowerCScale 3 body − 3,
q = 11·nearySideLowerC 3 body − 9·nearySideLowerCScale 3 body − 32.
```

For every nonempty body, the native ternary code gives `24<D` and `0<q<16D`. Lean proves

```text
det bridge(27, c(3z+1) b(3x+2) c(3y)) = 729/704 · P(D,q,x,y,z),
```

where `P` has the eight wait monomials `xyz,xy,xz,x,yz,y,z,1`. Its `xyz` and `xz`
coefficients are positive multiples of

```text
84797D − 2991q − 143568 > 0.
```

Five other coefficients are sums of manifestly positive terms after the same linear bounds.
The remaining `yz` coefficient is

```text
810465320D² + 59128288Dq + 2838157824D
  − 2871240q² − 275639040q − 6615336960.
```

Multiplying `q<16D` by `q>0` absorbs the negative quadratic term. Multiplying `24<D` by `q>0`
then absorbs the negative linear term, and the residual `D` polynomial is positive. Thus every
coefficient of `P` is strictly positive, so the bridge never closes for nonnegative waits.

## Proof Boundary

`ParabolicBlade.bridge_cOne_bTwo_cZero_det` substitutes the exact residue-one `c`, residue-two
`b`, and residue-zero `c` matrices into the checked bridge and normalizes the determinant.
`ParabolicBlade.cOneBDefectCZeroCore_pos` proves the coefficient inequalities from the native
code interval. `ParabolicBlade.bridge_cOne_bTwo_cZero_det_ne_zero` derives that interval for an
arbitrary nonempty body and closes the positive product. No body enumeration, floating-point
estimate, or unverified polynomial certificate enters the result.

## Scope

The theorem treats exactly three atoms at `β=3`, with a residue-one `c` left endpoint, one `b`
defect, and a residue-zero `c` right endpoint. The transposed double-`c` endpoint family,
simultaneous `c` defect and endpoint atoms, longer defect runs, and nontrivial safe contexts
remain outside the claim.

## Validation

The target `MatrixMortality.ParabolicMixedEndpoint` builds without warnings under Lean `4.33.1`.
Both public determinant theorems have axiom set exactly
`[propext, Classical.choice, Quot.sound]`. No proof aperture, external declaration, or linter
suppression was added.

## Artifact

[`MatrixMortality/ParabolicMixedEndpoint.lean`](../MatrixMortality/ParabolicMixedEndpoint.lean)
