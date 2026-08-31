# M₄(3) phase-zero right-`c` second-first-`b` extinction audit

**Date:** 31 August 2026

**Status:** the even-`b` `ccb` cylinder is formally extinct

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** close the first-`b`-after-two-`c` chamber left by the parity reduction

## Verdict

For every tail and every natural `x,y,z`, a body `ccb·tail` with an even total number of `b`
letters has nonzero primitive phase-zero right-`c` core. Consequently the corresponding
residual `b | b | c` bridge has nonzero determinant.

## Proof Boundary

The faces `y=0` and `y=1` are excluded directly. For `y≥2`, exact monotone envelopes trap the
outer wait in

```text
(5541372938576372618y−718629336347817375)
  /(25950255067173888y+30751845545334654)
≤ x <
(112032354356496y−14545738406053)
  /(524493688320y+618673335624).
```

Integer arithmetic compresses this window to 12 ranges containing 77 pairs `(x,y)`. Every tail
containing `b` has a unique first-`b` decomposition. Exact affine-rectangle arguments eliminate
all integral inner waits except `(x,y,z)=(213,465,38)` with tail prefix `ccb`. A separately
checked rational endpoint theorem places every continuation beyond that prefix in a strict
grammar gap, eliminating the final point.

The repository-owned generator uses `fractions.Fraction` only to derive the finite corner
certificate. Its emitted Lean proofs independently recheck each rectangle corner with
`norm_num`; `--check` rejects stale output. The certificate is sharded solely to satisfy source
size and line-length gates. No theorem depends on a temporary artifact or a runtime oracle.

## Scope

The theorem covers exactly `ccb·{b,c}*` in the even-`b` parity rectangle. Since the prefix
contains one `b`, even total count forces another `b` in the tail; this implication is itself
part of the Lean closure theorem. No even-length hypothesis is needed for the stronger local
statement. Other first-`b` positions and full `M₄(3)` mortality remain open.

## Validation

The generator freshness check and `MatrixMortality.ParabolicFirstBTwoClosure` build pass under
Lean `4.33.1`. The public theorems' transitive axiom sets are recorded in
`verification/axioms.txt`. No `sorry`, project axiom, unsafe declaration, proof aperture,
external declaration, or linter suppression was added.

## Artifacts

[`MatrixMortality/ParabolicFirstBTwo.lean`](../MatrixMortality/ParabolicFirstBTwo.lean),
[`MatrixMortality/ParabolicFirstBTwoReduction.lean`](../MatrixMortality/ParabolicFirstBTwoReduction.lean),
[`MatrixMortality/ParabolicFirstBTwoTail.lean`](../MatrixMortality/ParabolicFirstBTwoTail.lean),
[`MatrixMortality/ParabolicFirstBTwoClosure.lean`](../MatrixMortality/ParabolicFirstBTwoClosure.lean),
and
[`scripts/generate-parabolic-first-b-two-tail.py`](../scripts/generate-parabolic-first-b-two-tail.py)
