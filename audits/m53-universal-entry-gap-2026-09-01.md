# M₅(3) universal contraction-chamber entry audit

## Boundary

This audit classifies compiler-emitted swapped ternary role blocks that pull a carrier above the
terminal ray into the singleton-`D_c` Farey-contraction chamber. It proves neither that such an
entry is reachable from the encoded initial state nor that it is a pole.

## Chamber entry

Fix `β≥6`, set `ρ=3^β`, `r=ρ−2`, `H=5ρ−1`, and let the compiler body have length at
least `β−1` and begin in `b`. For a nonempty physical block, write `x` for its backward image
of any current carrier `X>H`. Lean proves

```text
1 < x < r/(r−3)  →  (x−1)/x < 1/(80ρ).
```

The proof has four cuts:

1. A lower spelling shorter than the punctuated upper spelling forces `x>7/5`, above the
   chamber. A longer lower spelling forces `x<1`. Every entrant therefore has equal spelling
   lengths.
2. The existing `MM-S87` theorem excludes every `b`-leading block.
3. At equal length, erasure-`c` and rule-`c` followed by `c` have lower code at least the upper
   code, contradicting `x>1`. A one-tile rule-`c` block is incompatible with the compiler-body
   length.
4. The surviving rule-`c`, `b` prefix has swapped upper code above `40ρ` times its suffix scale.
   Equal-length ternary words differ by less than half that suffix scale, yielding the factor
   `80ρ`.

The conclusion is uniform over the rest of the role word and the carrier `X`; no finite block
enumeration remains in the theorem.

## Successor intercept

For `ε=(x−1)/x`, `μ=2ρ−1`, and `Q=3^(β−6)`, define

```text
Ξ = μr²ε / [6μ+(r²+2r−6μ)ε].
```

Lean proves that `Ξ` is exactly the boundary coordinate obtained by passing the chamber
carrier through singleton `D_c`. The entry theorem implies

```text
0 < Ξ < 8Q/5.
```

This upper window is uniform but has no positive quotient-scale lower endpoint. Consequently it
does not by itself satisfy the two-sided intercept hypotheses of the `MM-S88` no-reentry
automaton.

## Discovery diagnostics

Before formalization, bounded enumeration at widths five through eight found no physical chamber
entry with unequal spelling lengths or relative gap at least `1/(80ρ)`. A separate 900,000-sample
long-word search, with role lengths up to 49, found none. These searches selected the invariant;
they are computational evidence only and are unnecessary for the theorem.

## Open seam

The remaining contraction question is arithmetic. The exact primitive `3H` channel from
`MM-S86` and the target-code divisor from `MM-S92` must either force a quotient-scale lower bound
for `Ξ`, allowing the `MM-S88` automaton to close, or expose a physical family with arbitrarily
small intercept. No reachability or pole conclusion follows from the present result.

## Verification

Formal sources:

- [`MatrixMortality/SwappedSetterEmptyFrontChamber.lean`](../MatrixMortality/SwappedSetterEmptyFrontChamber.lean)
- [`MatrixMortality/SwappedSetterUniversalEntryGap.lean`](../MatrixMortality/SwappedSetterUniversalEntryGap.lean)

Both sources compile without warnings. Their namespaces pass the default linters; every public
theorem is listed in `AxiomAudit.lean`; the reviewed axiom snapshot uses only standard axioms;
and the aperture scan is empty.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.
