# M₃(2) Cubic Selected-Cleanup Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S71` uses exactly one cleanup reader per clocked comparison. A sound compiler cannot assume
that count unless the selected incidence itself rejects every surplus or deficit.

## Balance

For `N` clock blocks, `m` cleanup readers, and `q=4/25`, the residual terminal ratio is
`ρ=qᴺ q⁻ᵐ`. If `S` is the signed mismatch radix, exact selector algebra reduces zero incidence
to

```text
S = (236474506444/1614375)(1-ρ).
```

The signed digit alphabet `{-1,0,1}` gives `|S|<25/21`. For `m<N`, the right side is at least its
value at `1-q=21/25`; for `m>N`, it is at most its value at `1-q⁻¹=-21/4`. Both lie strictly
outside the signed-radix interval. Thus `m=N`, after which the equation gives `S=0` and every
comparison matches.

Lean transports this exact exclusion through the physical terminal realization, common-ray
connector, selected row chart, nonzero scales, and source incidence. All physical waits are
positive, and balanced cleanup reproduces the `R32-S71` word exactly.

## Adjudication

| Claim | Judgment |
| --- | --- |
| arbitrary-cleanup affine normal form | Lean checked |
| uniform signed-radix bound | Lean checked |
| too-few cleanup exclusion | Lean checked |
| too-many cleanup exclusion | Lean checked |
| cleanup and matching balance biconditional | Lean checked |
| physical realization, positivity, and incidence | Lean checked |
| final zero iff cleanup count and all matches | Lean checked |
| complete block formation in raw waits | open |
| arbitrary raw-word converse | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: the fixed source selector enforces both matching and exact cleanup count
KILLED: cleanup multiplicity as an external obligation for complete clock schedules
EXPOSED: formation of the clock blocks themselves and the larger source-fibre quotient
NEXT: force or decode complete blocks inside arbitrary positive wait words
```
