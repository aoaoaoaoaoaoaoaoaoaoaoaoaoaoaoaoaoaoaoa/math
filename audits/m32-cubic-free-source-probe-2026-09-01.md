# M₃(2) Cubic Free Source-Probe Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S75` embeds a projectively free binary monoid into one separator-source fibre, but leaves
open whether this memory is merely hidden terminal state. This audit asks whether a positive
continuation can observe and decode every stored address.

## Probe

Appending the single positive wait `[1]` after the safe suffix exposes, in the transverse
common-ray basis, a nonzero multiple of

```text
(z,1)ᵀ,        z = -26658067/399826944.
```

For a binary address `β`, the resulting projective coordinate is

```text
χ(β) = (z + code(reverse β)) / ∏ ratio(βᵢ),
ratio(0)=1/625,           ratio(1)=197/336000.
```

## Decoder

The cleared affine numerator is never divisible by `197`; the exact finite-field obstruction is
that the affine residue orbit never reaches `114`. Therefore

```text
v₁₉₇(χ(β)) = -#₁(β),
```

so equality of coordinates recovers the one-count. The empty address is negative. Every
nonempty affine numerator is positive and lies in one explicit shell whose upper endpoint is
less than `625` times its lower endpoint. Equality after removing the common one-bit factor thus
recovers the zero-count. The denominator products now agree, so equality reduces to equality of
the affine radix codes; their existing injectivity recovers the complete ordered address.

## Physical Transport

For the fixed source-return prefix `Aword`, transverse encoding `E`, and safe suffix `S`, put

```text
Rβ = Aword ++ E(β) ++ S ++ [1].
```

The fixed prefix product is a unit. Cancelling it transports normalized coordinate injectivity
to the physical statement

```text
Π(Rα)c ∼ Π(Rβ)c   implies   α=β.
```

Every wait is positive and `|Rβ|=71,192+4|β|`.

## Adjudication

| Claim | Judgment |
| --- | --- |
| exact one-wait chart and physical scale | Lean checked |
| modulo-`197` noncancellation | Lean checked |
| valuation recovery of the one-count | Lean checked |
| empty/nonempty sign separation | Lean checked |
| positive shell and zero-count separation | Lean checked |
| complete affine-coordinate injectivity | Lean checked |
| physical positivity and exact length | Lean checked |
| projective source injectivity after fixed-prefix cancellation | Lean checked |
| composition with the selected zero comparator | open |
| arbitrary positive raw-word converse | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a positive one-symbol readout for the free binary source-stabilizer memory
KILLED: the claim that the exponential selected-source fibre is terminally unobservable
EXPOSED: an exact write/store/read channel in the fixed cubic companion
NEXT: route the decoded projective source into the selected mismatch-zero gate and close syntax
```
