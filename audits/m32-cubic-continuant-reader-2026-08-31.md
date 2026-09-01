# M₃(2) Cubic Continuant Reader Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S57` gives a free binary write stack in the fixed false-wait recurrence but no positive
operation that removes a digit. The missing operation is a reciprocal affine map realized by a
word over positive waits.

## Exact Readers

Write

```text
G₀=[[4,274/12],[0,25]],   G₁=[[4,149/12],[0,25]].
```

An exact terminal-loop search found reciprocal-ratio maps and translations of both signs. Lean
checks the following normalized factors:

```text
E₀=[[25/4,199285/6],[0,1]], P₀=[[1,2839/108],[0,1]],
N₀=[[1,−189665/144],[0,1]],

E₁=[[25/4,9159/500],[0,1]], P₁=[[1,31457/6480],[0,1]],
N₁=[[1,−266051/303750],[0,1]].
```

Their physical words have lengths `35,30,34` and `33,23,37`, respectively. Every wait is
positive and every erased physical scale is nonzero. The Diophantine corrections are

```text
N₀²⁶P₀³⁹E₀=[[25/4,−274/48],[0,1]]=R₀,
N₁³⁰P₁E₁   =[[25/4,−149/48],[0,1]]=R₁.
```

The resulting physical readers have lengths `2089` and `1166`. Direct multiplication gives

```text
R₀G₀=25I,   R₁G₁=25I.
```

The formal proof keeps the fixed blocks and their repetition counts symbolic. It proves each
block product directly, proves the power law for upper translations, composes nonzero physical
scales, and then derives correct head deletion for an arbitrary physical suffix.

## Mismatch Audit

The readers do not supply local soundness:

```text
R₀G₁=25[[1,−125/48],[0,1]],
R₁G₀=25[[1, 125/48],[0,1]].
```

The defects are nonzero but opposite. Their product is `625I`, and Lean lifts this normalized
identity to the full positive physical spelling. Two wrong reads can therefore masquerade as two
correct reads under any terminal test that sees only the projective product.

## Adjudication

| Claim | Judgment |
| --- | --- |
| all reader letters are positive waits | Lean checked |
| the six fixed terminal-loop blocks have the displayed normalized forms | Lean checked |
| the repeated corrections give exact inverses of both radix letters | Lean checked |
| a correct reader preserves every following suffix up to a nonzero scalar | Lean checked |
| the reader pops every `R32-S57` encoding head | Lean checked |
| one wrong read is locally nontrivial | Lean checked |
| two opposite wrong reads cancel projectively | Lean checked, including physical words |
| the readers alone form a sound stack compiler | rejected |
| an independent mismatch trap exists in the same fixed family | open |
| the complete cubic continuant language or `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: the write-only obstruction for the fixed cubic radix stack
GAINED: positive exact projective inverses for both binary digits
EXPOSED: the unique affine soundness defect, with opposite mismatches cancelling exactly
NEXT: trap the signed parabolic defect locally, or exploit a source grammar that forbids its cancellation
```
