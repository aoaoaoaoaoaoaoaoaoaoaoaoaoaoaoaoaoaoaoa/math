# M₄(3) residue-zero `c`-endpoint audit

**Date:** 30 August 2026

**Status:** both shortest bad-run orientations are excluded when a `b` defect has a residue-zero
`c` endpoint

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** extend `M4-S09` from all-`b` atoms to the first body-dependent endpoint placements

## Verdict

At deletion width three, write `L` and `M` for the lower code and scale of an arbitrary nonempty
body. Lean computes

```text
det K(c(3z)b(3x+2)b(3y+1))
  = (729y/2)(Cₓ𝓏xz + 294449472x + C𝓏z + 11485615704),

Cₓ𝓏 = 126321120L + 13935744M − 168128352,
C𝓏  = 4989792861L + 507644678M − 6512726895,
```

and

```text
det K(b(3z+1)b(3x+2)c(3y))
  = −312741z(104016(M−3)xy + 312048x + Cᵧy + 4989566),

Cᵧ = 2857811L − 68818M − 2651357.
```

The checked native inequality `0<11L−9M−32<16(M−3)` makes `M−3`, `Cₓ𝓏`, `C𝓏`, and `Cᵧ`
strictly positive. The two brackets are therefore positive for all nonnegative waits. Regularity
requires `y>0` in the first orientation and `z>0` in the second, since the zero wait would be the
exceptional singular endpoint `b(1)`. Both determinants are nonzero.

## Proof Boundary

`ParabolicBlade.bridge_cZero_bTwo_bOne_det` and
`ParabolicBlade.bridge_bOne_bTwo_cZero_det` substitute the exact residue matrices into the
checked bridge definition and normalize the determinants. Their nonzero corollaries use only
`ParabolicBlade.neary_rule_c_residue_one_bounds`, wait nonnegativity, and the stated regularity
hypothesis. No body enumeration, floating-point estimate, or unverified polynomial certificate
enters the result.

## Scope

The result treats exactly three atoms at `β=3`, with a `b` defect and exactly one `c` endpoint in
residue-zero phase. It does not cover a residue-one `c` endpoint, a `c` defect together with a
`c` endpoint, a defect run longer than one, or a nontrivial safe context at either endpoint.

## Validation

The target `MatrixMortality.ParabolicDefect` builds without warnings under Lean `4.33.1`. The
four public theorems have axiom set exactly `[propext, Classical.choice, Quot.sound]`. No proof
aperture, external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicDefect.lean`](../MatrixMortality/ParabolicDefect.lean)
