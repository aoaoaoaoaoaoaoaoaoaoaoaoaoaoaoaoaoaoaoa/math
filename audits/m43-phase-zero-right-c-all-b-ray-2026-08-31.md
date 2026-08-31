# M₄(3) phase-zero right-`c` all-`b` ray audit

**Date:** 31 August 2026

**Status:** every nonempty all-`b` body is excluded in the `0|2|1` `b|b|c` family

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** eliminate the all-`b` half of the even/even residue left by `M4-S21`

## Verdict

For `body=b^n`, the encoded coordinates satisfy

```text
length(tagEncode₃(body)) = 5n,
242C = 203(S−1),
242(S−C−1) = 39(S−1).
```

Odd `n` already falls to `M4-S19`. For even `2≤n<14`, exact residue factorizations make the
normalized core respectively `8` modulo `16`, `16` modulo `32`, or `32` modulo `64`.

For `n≥14`, the normalized core is affine in `z`, say

```text
(Sa+b)z + Sc+d.
```

Any zero first forces `x≤203` and `1≤y<10000`. The slope `a` is 72 times an odd integer, so
it is nonzero. The affine resultant factors as

```text
ad−bc = −1926044220672 y (48x−3029)
          (674088x−4333144y−1095244575),
```

and is nonzero. On the forced rectangle, `|b|<10¹⁸` and `|ad−bc|<10³¹`, whereas
`S≥243¹⁴` makes `|Sa+b|>10³¹`. An integral zero would make `Sa+b` divide the
resultant, a contradiction. Thus every even all-`b` body is also excluded.

## Proof Boundary

`ParabolicBlade.bridge_bZero_bTwo_cOne_det_ne_zero_of_b_run` proves the complete ray. Its large
case uses exact integer inequalities and the displayed resultant; its six small cases use exact
polynomial residue identities. No wait box, floating-point approximation, or unproved
primitive-divisor assertion enters the proof.

## Scope

The theorem treats deletion width three, exactly three atoms, orientation `0|2|1`, letters
`b|b|c`, every nonempty all-`b` body, and every natural wait triple. Mixed bodies, the other
shortest families, longer defect runs, and nontrivial safe contexts remain open.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorem's transitive axiom set is recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
