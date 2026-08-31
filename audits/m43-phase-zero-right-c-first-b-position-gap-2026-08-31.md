# M₄(3) phase-zero right-`c` first-`b` position-gap audit

**Date:** 31 August 2026

**Status:** every consecutive first-`b` density gap is formally empty

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** replace repeated finite prefix casework by one exact grammar theorem

## Verdict

For every natural threshold `k` and every physical tag body, let `S` be its encoded ternary
scale and `D=S−C−1` its complement. Lean proves

```text
13S ≤ 81·3^kD
  or
242·3^(k+1)D < 39S.
```

Thus no physical complement density lies in the open interval between the first-`b` cylinders
at positions `k` and `k+1`.

## Proof Boundary

The proof is a simultaneous structural analysis of the threshold and leading tag letter. A
leading `b` uses the exact first-`b` lower endpoint. A leading `c` preserves the complement and
triples the scale, transporting the previous threshold's dichotomy. At threshold zero, the
global complement bound supplies the strict later-position inequality. The empty and all-`c`
words lie on the strict-low side.

No determinant identity, bounded word search, or approximate comparison enters the theorem.
The lower endpoint remains weak and the upper endpoint remains strict.

## Scope

The theorem applies to every finite word over `{b,c}` and every threshold `k`. It is a grammar
statement about the native ternary tag encoding, not a nonvanishing result by itself.

## Validation

`MatrixMortality.ParabolicEvenBody` builds without warnings under Lean `4.33.1`. The theorem's
transitive axiom set is recorded in `verification/axioms.txt`. No proof aperture, external
declaration, or linter suppression was added.

## Artifact

[`MatrixMortality/ParabolicEvenBody.lean`](../MatrixMortality/ParabolicEvenBody.lean)
