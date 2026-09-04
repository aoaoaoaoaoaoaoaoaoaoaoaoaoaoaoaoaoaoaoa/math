# M₃(2) Exact Binary-Pump Comparator Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S80` and `R32-S81` give positive inverses of both free transverse-pump digits. This audit
asks whether placing every reader before every writer yields an exact arbitrary-depth word
comparison, rather than another cancellative affine quotient.

## Phased Comparator

For a guessed word `γ`, reverse its bits and replace each by its positive physical inverse.
Append the forward writer encoding of `β`. Letterwise two-sided cancellation proves that the
normalized product is identity when `γ=β`.

For the converse, multiply a putative projective identity by the normalized writer product of
`γ`. This gives projective equality of the writer products of `β` and `γ`; the `R32-S67`
projective-freeness theorem forces `β=γ`. Lean then transports the biconditional to the literal
physical word. Since every positive-wait product is a unit, Lean also cancels arbitrary positive
prefixes and suffixes and proves that no surrounding positive context weakens this converse.

All inverse readers precede all writers, so the theorem does not admit the interleaved local
mismatch cancellations. The exact physical length is the sum of `37681` for each false guessed
bit, `306510` for each true guessed bit, and four returns for each written bit. Every wait is
positive.

## Adjudication

| Claim | Judgment |
| --- | --- |
| normalized reverse inverse cancels forward product | Lean checked |
| forward product cancels reverse inverse | Lean checked |
| normalized projective identity iff words agree | Lean checked |
| physical inverse-encoding chart | Lean checked |
| physical comparator chart | Lean checked |
| literal physical projective identity iff words agree | Lean checked |
| arbitrary positive prefix-and-suffix contextual converse | Lean checked |
| positivity and exact variable-rate length | Lean checked |
| unguarded first-hit safety | open |
| arbitrary raw-word phase enforcement | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: an exact arbitrary-depth positive whole-word equality comparator
KILLED: affine mismatch cancellation inside the all-readers-before-all-writers language
EXPOSED: first-hit masking and raw phase enforcement as the remaining operational seams
NEXT: append the one-wait probe guard and prove closure of every matched neutral block string
```
