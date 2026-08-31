# Separated Four-C Reproduction Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The final `n≡11 (mod 27)` diagonal class contains a canonical four-active-`c` block with an
exact two-copy reproduction law. In its first subresidue, `n≡11 (mod 81)`, the reproduced
blocks both miss every deletion head, so the coupled queue halts. Only `n≡38,65 (mod 81)`
remain open on the diagonal.

## Canonical Block

Write `n=3A-1`, assume `A≡1 (mod 3)`, and choose `m` with `3m=4A-1`. Define

```text
B_A = c b^(3A-1) c b^(4A+1) c b^(3A-1) c.
```

The exact four-event history processes the successive internal gaps with unary stroke counts

```text
A-1, m, A-1.
```

The fourth `cbb` stroke completes the macro. For every unary tail `T`, Lean proves

```text
B_A b^T  →*  b^T B_A b^(3A+m+2) B_A b^(3A).
```

This is not a numerical trace. The formal proof exposes three named intermediate queues and
composes four exact reachability certificates.

## Modulo-Eighty-One Cut

In the first surviving `MM-S41` subresidue, put

```text
A = 27k+4,
m = 36k+5,
n = 81k+11.
```

The six-event queue from `MM-S41` has a prefix of length `3(165k+26)` whose every
width-three head is `b`. Canonical chunk execution consumes that prefix and appends
`165k+26` copies of `b`, exposing

```text
B_A b^(246k+38).
```

Applying the reproduction law places the first block in phase two and the second in phase one
modulo three. Neither phase is a deletion head. An offset-indexed invariant checks all eight
`c` positions; the constant-head theorem then drains the queue.

## Checked Boundary

[`MatrixMortality/SeparatedTwoCResidueTwo.lean`](../MatrixMortality/SeparatedTwoCResidueTwo.lean)
kernel-checks the reusable `fourCBlock`, `fourCQueue`, and `fourCExpansion` definitions, the
exact theorem `SeparatedTwoCResidue.fourCQueue_reaches_final`, and the halting theorem
`SeparatedTwoCResidue.elevenModuloEightyOne_tagHaltsFrom`.

The result does not decide the two surviving tail phases, unequal separated runs, arbitrary
two-`c` bodies, or deletion-width-three universality.
