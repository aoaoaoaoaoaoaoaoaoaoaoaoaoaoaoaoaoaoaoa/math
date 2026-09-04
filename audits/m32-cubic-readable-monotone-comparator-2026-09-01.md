# M₃(2) Readable Monotone-Comparator Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

Raw false/true and true/false reader errors produce opposite translations and can cancel.
`R32-S78` separately rejects a nonempty free-memory payload. This audit asks whether positive
words can make both defects monotone and combine them in one exact zero gate.

## Unsigned Checks

Positive terminal-translation count vectors `(391,9,596,1500)` and `(606,12,177,1125)` realize
`T(173/48)` and `T(-77/48)`. Appending the appropriate correction to each reader-writer block
makes a match projectively `T(0)` and either orientation of a mismatch projectively `T(1)`.
A list of corrected blocks is therefore `T(m)`, where `m` is its ordinary mismatch count.

Inside the height-five selector this shifts the selected row by `+(15/68)m`. For source address
`00++payload`, the one-wait coordinate gap above the selected `00` coordinate is nonnegative and
is zero exactly when `payload=[]`. The normalized incidence is their sum times a nonzero ratio
product. It follows that the complete physical gate vanishes exactly when the payload is empty
and every check matches.

## Physical Certificate

Every wait in every component is positive. The local costs for checks `00,01,10,11` are
`2090,83342,65451,1175`, and the complete gate length is

```text
535731821 + Σ checkCost(Cᵢ) + 4|payload|.
```

## Adjudication

| Claim | Judgment |
| --- | --- |
| two exact correction shifts and nonnegative certificates | Lean checked |
| four corrected local reader-writer identities | Lean checked |
| schedule equals translation by mismatch count | Lean checked |
| mismatch count is zero iff every check matches | Lean checked |
| height-five transport and positive row shift | Lean checked |
| exact marker-coordinate gap and its zero set | Lean checked |
| normalized cancellation-free AND gate | Lean checked |
| complete physical zero biconditional | Lean checked |
| positivity and exact local and total lengths | Lean checked |
| arbitrary raw-word parsing | open |
| complete undecidable source-machine compiler | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: one positive physical gate enforcing empty memory and every comparison simultaneously
KILLED: opposite mismatch cancellation and explicit cleanup as obligations of this segmented gate
EXPOSED: arbitrary-word syntax, not local arithmetic, as the sharp remaining converse
NEXT: force or classify block boundaries in every accepting positive-wait word
```
