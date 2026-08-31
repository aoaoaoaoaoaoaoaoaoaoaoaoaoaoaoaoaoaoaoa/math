# M₄(3) phase-zero right-`c` first-`b` density audit

**Date:** 31 August 2026

**Status:** every first-`b` position owns an exact complement-density cylinder

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace arbitrary prefix languages by rational coordinate intervals

## Verdict

For physical tag words `u,v`, Lean proves

```text
D(uv)=D(u)3^length(encode(v))+D(v).
```

If a word begins with `j` copies of `c` followed by its first `b`, then

```text
13S ≤ 81·3^jD,
242·3^jD < 39S.
```

Thus its complement density lies in the exact half-open interval

```text
[13/(81·3^j), 39/(242·3^j)).
```

## Proof Boundary

A direct positional calculation gives `D(bv)=39S(v)+D(v)`. The lower bound discards the
nonnegative suffix complement. The upper bound substitutes
`242D(v)≤39(S(v)−1)` and retains the strict `39` gap. Scaling by the leading `c` run gives
the displayed cylinder.

No root estimate, bounded body search, or floating-point comparison enters this result.

## Scope

This is a structural theorem about the deletion-width-three tag encoding. It constrains every
physical suffix, but it does not assert nonvanishing of the right-`c` determinant without an
additional corner argument.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The public
theorems' transitive axiom sets are recorded in `verification/axioms.txt`. No proof aperture,
external declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
