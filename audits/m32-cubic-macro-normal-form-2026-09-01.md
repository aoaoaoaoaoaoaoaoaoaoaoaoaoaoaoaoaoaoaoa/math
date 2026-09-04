# M₃(2) Cubic Reader-Writer Normal-Form Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The selected comparator admits projectively scalar insertions. The bounded search found no
nonneutral collision inside the four normalized radix writers and readers, but bounded evidence
cannot establish a quotient. This audit constructs the exact all-word normal form for that
restricted alphabet.

## Normal Form

Normalize each writer and reader to an upper affine matrix with lower-right entry one. With
`q=4/25`, each letter has multiplier `q` or `q⁻¹`. A word evaluates recursively to

```text
N(ε)=(0,0),
N(a·w)=(h(a)+h(w), s(a)+q^h(a)s(w)).
```

Lean proves

```text
Π(w)=[[q^N(w).height,N(w).shift],[0,1]].
```

The lower-right entry forces the projective scale to one, and powers of `4/25` are injective on
integer exponents. Therefore two normalized products are projectively equal exactly when their
normal forms agree. Nonzero physical realization scales transport the same biconditional to the
positive wait spellings.

A word is projectively scalar exactly when both fields vanish. Reversal with writer-reader
exchange gives an exact two-sided inverse, and the quotient word is neutral exactly when the two
original products agree. The `R32-S71` opposite-mismatch word evaluates to `(0,0)`.

## Adjudication

| Claim | Judgment |
| --- | --- |
| affine semidirect-product evaluator | Lean checked |
| exact normalized product | Lean checked |
| nonzero physical realization and positivity | Lean checked |
| normalized projective equality iff normal equality | Lean checked |
| physical projective equality iff normal equality | Lean checked |
| neutral-kernel classifier | Lean checked |
| exact inverse and quotient laws | Lean checked |
| opposite-mismatch witness normal form | Lean checked |
| larger known macro dictionary | excluded |
| arbitrary raw-wait segmentation | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a complete decidable projective quotient for the four reader-writer macros
KILLED: scalar-kernel ambiguity after lawful segmentation in that alphabet
EXPOSED: the larger double-coset fibre and arbitrary raw-word recognition
NEXT: extend the fibre analysis without conflating restricted macro completeness with raw syntax
```
