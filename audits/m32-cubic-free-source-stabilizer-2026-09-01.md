# M₃(2) Cubic Free Source-Stabilizer Audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`R32-S72` proves one non-scalar right stabilizer of the separator source. A cyclic or otherwise
small stabilizer quotient might still make the selected source fibre tractable. This audit tests
whether the existing transverse binary pump embeds free memory into that fibre.

## Return

The four available positive terminal translations satisfy

```text
1003(2839/108) + 24(-189665/144)
  + 1148(31457/6480) + 375(-266051/303750) = -41/90.
```

Thus one positive word of length `71,185` realizes `A=T(-41/90)`. Exact multiplication gives

```text
A(4,3)ᵀ = -(1/30)(-79,-90)ᵀ.
```

The safe suffix `S=[15,29,11,13,7,8]` maps the separator source to a nonzero multiple of `(4,3)ᵀ`.
Every transverse binary pump word preserves that ray by a nonzero scale. Hence

```text
Wβ=Aword ++ E(β) ++ S
```

stabilizes the original source projectively for every binary address `β`.

## Freeness

All waits in `Aword`, `E(β)`, and `S` are positive, so the fixed prefix and suffix products are
units. Cancelling them from a projective equality between `Wα` and `Wβ` leaves a projective
equality between `E(α)` and `E(β)`. The existing transverse-pump theorem then gives `α=β`.

Prefixing the selected `00` source preserves both the common source ray and projective
injectivity. Width `n` therefore gives exactly `2^n` words of common length `71,199+4n`, with
pairwise projectively distinct matrix products and one observed source ray.

## Adjudication

| Claim | Judgment |
| --- | --- |
| four-generator translation count-vector abstraction | Lean checked |
| exact shift `-41/90` and physical realization | Lean checked |
| source-return ray identity | Lean checked |
| positivity and exact lengths | Lean checked |
| all-address source stabilization | Lean checked |
| projective injectivity after unit cancellation | Lean checked |
| selected-fibre `2^n` family at every width | Lean checked |
| global minimality of the displayed count vector | computational only |
| arbitrary raw-word converse | open |
| `M₃(2)` is decided | open |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
GAINED: a projectively free positive binary monoid inside the separator-source stabilizer
KILLED: finite, scalar, or cyclic quotients of the selected source fibre
EXPOSED: unbounded hidden memory that must be read later or assigned lawful epsilon semantics
NEXT: compose a positive context that reads this source-stabilizer payload
```
