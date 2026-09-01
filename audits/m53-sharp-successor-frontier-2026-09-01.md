# M₅(3) sharp post-contraction successor audit

## Boundary

This audit sharpens `MM-S93` and runs its post-`D_c` carrier through one arbitrary further
physical role block. It classifies the unresolved successor spellings; it proves neither
encoded-entry reachability nor a pole.

## Exact prefix gap

The sole equal-length chamber entrant retained by the `MM-S93` proof starts with rule `c`
followed by a `b`-letter tile. Its common swapped ternary prefix has exact value

```text
code(1 H(b)̅ 1)=45ρ−5.
```

The two equal-length suffixes differ by less than half their common scale. For the backward
image `x`, Lean therefore strengthens the relative-gap bound to

```text
ε=(x−1)/x < 1/(90ρ−10).                         (1)
```

The earlier `1/(80ρ)` result remains as a corollary.

## Affine ceiling

The post-`D_c` boundary intercept

```text
Ξ=μr²ε/[6μ+(r²+2r−6μ)ε]
```

is strictly increasing for positive `ε`. Evaluating its rational cap at the right side of (1)
and writing `Q=3^(β−6)` gives

```text
β=6:  Ξ < 2−H/(9ρ−1),
β≥7:  Ξ < 14Q/9−H/(9ρ−1).                 (2)
```

For `β≥7`, the cleared numerator of (2), after shifting `Q` by three, is

```text
65969168886396
+255323030245680 s
+211364320377402 s²
+65575081072044 s³
+7015410214812 s⁴,
```

where `s=Q−3≥0`; positivity is coefficientwise.

## Successor frontier

The exact physical upper-code automaton from `MM-S88` applies to the arbitrary intercept (2).
Lean proves:

- every `c`-leading next block has negative backward slope;
- for `β≥7`, every `b`-leading next block has slope below one unless its lower spelling is
  shorter than the quotient-shifted upper scale;
- at `β=6`, the only additional survivor is the critical rule-`b` prefix chamber
  `14A≤9V` and `3V<5A`.

Thus every next contraction candidate lies in the short-lower chamber or the one width-six
critical prefix. The theorem composes this classification directly from an arbitrary physical
first chamber entry; no canonical `(R_c,D_b)` hypothesis remains.

## Lower-bound no-go

A direct replacement of the canonical `MM-S88` lower intercept bound is false. Exact
enumeration at width six finds the full-`3H` physical entrant

```text
body = bcbbb,
target = c⁶,
block = R_c D_b⁴,
Ξ ≈ 0.7826195533 < 6/5.
```

The uniform computational family

```text
body = b c b^(β−3),
target = c^β,
block = R_c D_b^(β−2)
```

passes the exact `3H` channel for `5≤β≤12`; its ratio `Ξ/Q` increases toward approximately
`0.9`. This family is computational evidence only. The formal frontier uses no lower intercept
claim.

## Open seam

The surviving problem is no longer an arbitrary-word Archimedean classification. It is the
short-lower spelling chamber, together with one finite-width critical prefix. Their extinction
must use the exact primitive `3H` channel, the `MM-S92` target modulus, or earlier-pole ancestry.

## Verification

Formal sources:

- [`MatrixMortality/SwappedSetterPostRcDbChamber.lean`](../MatrixMortality/SwappedSetterPostRcDbChamber.lean)
- [`MatrixMortality/SwappedSetterUniversalEntryGap.lean`](../MatrixMortality/SwappedSetterUniversalEntryGap.lean)

Both sources compile without warnings. Their namespaces pass the default linters; every public
theorem is listed in `AxiomAudit.lean`; the reviewed axiom snapshot uses only standard axioms;
and the aperture scan is empty.

## Authorship

GPT-5.6 Sol, elicited by @eternalism_4eva.
