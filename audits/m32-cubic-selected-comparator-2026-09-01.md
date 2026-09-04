# M₃(2) Cubic Selected-Comparator Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S59` checks a designated schedule of radix reads and writes. `R32-S70` selects one encoded
source address. The first question is whether these mechanisms compose without losing their
exact converse. The second is whether the result enforces its block spelling against arbitrary
positive raw words.

## Composition

For a check schedule `χ`, let `δχ` be its signed mismatch defect. The balanced physical checker
realizes `T((125/48)δχ)`. Combining it with the singleton translation and applying the common-ray
connector gives

```text
Fχ=[[1,−85828079/1020+(625/1088)δχ],
    [0,                         9/340]].
```

The fixed prefix row becomes

```text
[1,s(00)+(625/1088)δχ].
```

Since the lower coordinate of the normalized `00` source is nonzero, this row annihilates the
source exactly when `δχ=0`. The checked signed-radix decoder then proves

```text
r Π(C(χ) ++ E(00)) c = 0
  iff every guessed bit equals its written bit.
```

Lean checks the terminal realization, common-ray chart, row law, nonzero projective scales,
physical incidence, biconditional, and positivity of every physical wait.

## Fracture

The word

```text
J=R₀G₁R₁G₀
```

contains two opposite wrong reads and no separate clock block. The earlier reader algebra gives

```text
Π(J)=λI,       λ≠0.
```

Lean additionally proves every wait in `J` is positive and `|J|=3265`. Let `Z` be the singleton
selector word with wait-zero separators at both ends. Exact outer-product algebra and the
singleton incidence theorem give `Π(Z)=0`. Projective-identity insertion then gives a distinct
raw word `Z_J` with

```text
Π(Z_J)=0.
```

This is a malformed literal spelling, not a failure of the local comparator theorem: `J` was
inserted outside its designated schedule.

## Adjudication

| Claim | Judgment |
| --- | --- |
| mismatch-dependent terminal translation | Lean checked |
| selected common-ray loop and row | Lean checked |
| normalized matching biconditional | Lean checked |
| physical matching biconditional and positivity | Lean checked |
| opposite-mismatch scalar identity | Lean checked |
| identity positivity and length `3265` | Lean checked |
| designated and malformed punctuated zeros | Lean checked |
| literal inequality of the two zero words | Lean checked |
| converse modulo projective-neutral insertion | open |
| complete arbitrary-word compiler | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: one positive physical pipeline combining read, compare, and exact source selection
KILLED: literal block syntax as an arbitrary-word converse for that pipeline
EXPOSED: quotient decoding modulo projective-neutral epsilon stutters
NEXT: construct a complete neutral-congruence normal form or an observable control extension
```
