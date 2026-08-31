# Nonempty-Marker All-Erasure Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every all-erasure word containing at least one `D_b` misses the next multi-role
pole from a lawful two-`c` raw head

## Rightmost Marker

Every binary tag word with nonempty `b` support has a unique decomposition

```text
w = u · b · c^t,
```

where `u` may itself contain any number of `b` markers. Factoring the punctuated upper code at
the common suffix after the displayed rightmost marker gives

```text
P(w) − P(c^|w|) = D(u)·10^(t+β+2).                           (1)
```

The coefficient is always a five-adic unit with fixed residue:

```text
D(u) ≡ 2 (mod 5).                                           (2)
```

Indeed, the encoded prefix in `D(u)` is shifted by `β+1` decimal places, the same-width
all-`c` prefix code is divisible by `5`, and the marker code is `2` modulo `5`. Earlier markers
therefore change only the integer coefficient above the rightmost suffix; they cannot create a
competing shallow depth or alter (2).

For `k=#_b(w)≥1`, the exact physical depth of the prospective pole is

```text
m(w) = |tagEncode_β(w)|−1 = |w|+k(β+1)−1.                 (3)
```

The shell at (3) implies divisibility by `5^(|w|+β)`. Earlier markers therefore deepen the
physical shell while remaining absorbed into the coefficient in (1).

## Exhaustion

If `|u|≤β`, equation (1) reaches the width-level obstruction. If the raw head is regular, it
reaches the uniform depth-`β` obstruction in every position. The remaining case has
`|u|>β` and the exceptional raw head, where (1)–(3) satisfy the exact MM-S47 divisibility and
coefficient theorem. Its strict depth orders, two resonance arms, and common corner are all
impossible.

The lower spelling of any all-erasure tag word is the pure zero word of the same role length,
so no body-dependent lower correction reopens a case.

## Scope

The result covers an arbitrary finite all-erasure word over `{D_b,D_c}` with at least one
`D_b`, the lawful two-`c` raw head, and a following multi-role pole. It does not cover pure
all-`D_c` words, blocks containing a rule tile, singleton targets, or later generalized
carriers.

## Verification

`MatrixMortality/DecimalSetterPositioned.lean` checks the rightmost-marker decomposition,
exact common-suffix factor, fixed coefficient residue, arbitrary all-zero lower spelling, the
three physical depth regimes, and the unrestricted marker-support corollary. Narrow and root
builds, Lean language-server diagnostics, namespace lint, and selected transitive axiom
snapshots pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterPositioned.lean`](../MatrixMortality/DecimalSetterPositioned.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s49-nonempty-marker-all-erasure-extinction)
