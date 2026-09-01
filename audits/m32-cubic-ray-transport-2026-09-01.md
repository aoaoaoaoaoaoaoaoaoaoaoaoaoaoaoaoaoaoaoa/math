# M₃(2) Cubic Common-Ray Transport Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S68` makes the free binary pump readable at the original separator source, but mortality
still needs a positive left context that annihilates one selected source ray. Existing terminal
translations provide positive physical syntax; the question is whether they can be transported
into the pump's common-ray chart with useful signed affine action.

## Connector

For the common-ray basis `B=[[4,1],[3,1]]` and any upper-triangular terminal matrix
`H=[[a,b],[0,d]]`, Lean proves

```text
B⁻¹Π(1,15,8)HΠ(13)B =
  [[1057536000a, 515808000a+233280000b−195955200d],
   [0,             27993600d]].
```

For `a≠0`, its normalized affine chart is

```text
[[1, 199/408+(15/68)(b/a)−(63/340)(d/a)],
 [0,                         (9/340)(d/a)]].
```

Lean transports every projective physical realization of `H` through this identity and proves
that strictly positive middle words remain strictly positive after adding the connectors.

## Signed Digits

The two wait-positive terminal translations

```text
[[1,−189665/144],[0,1]],     [[1,2839/108],[0,1]]
```

therefore yield positive physical common-ray loops

```text
F₋=[[1,−4736689/16320],[0,9/340]],
F₊=[[1,    74677/12240],[0,9/340]].
```

Lean checks both physical projective realizations, positivity of every wait, equality and strict
contractivity of the ratios, and the two strict digit signs.

## Unsafe Expansion

Transporting `Π(5,5)` gives

```text
B⁻¹Π(1,15,8,5,5,13)B =
  609140736000·[[1,15529/6528],[0,1125/1088]].
```

The transverse ratio exceeds one, but the terminal suffixes are already accepting:

```text
Π(13)(4,3)       = −408(1,0),
Π(5,13)(4,3)     = 9792(1,0),
Π(5,5,13)(4,3)   = −235008(1,0).
```

Lean checks the chart, expanding inequality, full-loop ray eigenvalue, exact suffix images, and
their annihilation by the separator row.

## Adjudication

| Claim | Judgment |
| --- | --- |
| generic terminal-to-common-ray connector law | Lean checked |
| normalized affine transport formula | Lean checked |
| projective realization and positivity transport | Lean checked |
| opposite-signed equal-ratio positive physical digits | Lean checked |
| short expanding common-ray loop | Lean checked |
| all three accepting suffix images | Lean checked |
| selected separator-source annihilator | open |
| arbitrary-word compiler converse | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a generic positive transport from terminal triangular arithmetic to the free pump chart
KILLED: positivity as an obstruction to signed common-ray digits
EXPOSED: exact target-slope synthesis and first-hit safety as independent obligations
NEXT: classify the signed affine orbit against the R32-S68 source coordinates
```
