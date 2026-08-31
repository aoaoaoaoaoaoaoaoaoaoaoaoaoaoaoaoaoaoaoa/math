# Separated Two-C Residue-Eight Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The coupled width-three diagonal family

```text
qₙ = bb c bⁿ c bⁿ
```

halts for every `n≡8 (mod 9)`. This is an infinite halting stratum inside the separated
two-`c` source boundary. It complements the periodic residues proved by `MM-S25` without
classifying the remaining diagonal residues or the general separated family.

## Exact Certificate

Write `n=9k+8`. The proof uses the stroke history

```text
cbb, (bbb)^(3k+2), cbb, (bbb)^(3k+3), cbb, (bbb)^(3k+2), cbb.
```

Lean verifies its global history equation against the prescribed input `qₙ.drop 2 · b`. The
residual queue is a concatenation of unary runs with lengths divisible by three, four `bbc`
blocks, two `bcb` blocks, and one final unary run. Hence every letter at an index divisible by
three is `b`.

The production of `b` is the singleton word `b`. The repository's generic
`tagHaltsFrom_of_constantAtMultiples` theorem therefore drains the residual queue: every step
deletes three letters and appends one `b`, while every possible head remains `b`. Concatenating
the certified history with this draining execution proves termination from the coupled source.

## Checked Boundary

[`MatrixMortality/SeparatedTwoCResidue.lean`](../MatrixMortality/SeparatedTwoCResidue.lean)
proves `SeparatedTwoCResidue.eightResidue_tagHaltsFrom` for every `k`. Its proof depends only on
exact list identities, Presburger arithmetic, the verified tag-history semantics, and the
constant-head drainage theorem.

Together with `MM-S25`, this leaves `n≡2,5 (mod 9)` unresolved in the diagonal family. Bodies
with unequal outer runs and bodies containing at least three `c` letters also remain open. No
claim of deletion-width-three universality or full two-`c` decidability is made.
