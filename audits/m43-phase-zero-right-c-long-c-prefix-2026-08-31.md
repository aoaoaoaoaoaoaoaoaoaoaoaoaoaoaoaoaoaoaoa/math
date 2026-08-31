# M₄(3) phase-zero right-`c` long-leading-`c` audit

**Date:** 31 August 2026

**Status:** every mixed body with at least twelve leading `c` letters is excluded

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** turn the unbounded first-`b` direction into finitely many prefix cylinders

## Verdict

For the complement coordinate `D=S−C−1`, Lean proves

```text
D(c^k w)=D(w).
```

The same prefix multiplies the code scale by `3^k`. If `w` contains `b`, its complement is
positive and obeys the sharp global bound `242D≤39(T−1)`, where `T` is the tail scale.
The exact numerical inequality

```text
2160000·39 < 242·3^12
```

therefore puts every `c^k w` with `k≥12` inside the `M4-S27` thin-complement cone. Its bridge
determinant is nonzero for every natural wait triple.

## Proof Boundary

`tagComplementCode_cons_c` is a direct positional-code calculation.
`tagComplementCode_replicate_c_append` iterates it, and
`tagComplementCode_pos_of_mem_b` follows the exact right-append recurrences through a reverse
word induction. The public determinant theorem combines these identities, the already checked
global density bound, monotonicity of `3^k`, and `M4-S27`.

No finite body search or trailing 3-adic claim enters this theorem. In particular, reduced
congruence classes must be used before deriving any future trailing-run bound.

## Scope

The result concerns the deletion-width-three, three-atom, phase-zero right-`c` family and mixed
bodies with the stated prefix. It gives a coarse first-`b` cutoff, not a classification of the
remaining twelve prefix cylinders.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
