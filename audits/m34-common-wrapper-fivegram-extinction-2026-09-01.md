# M₃(4) Explicit Common-Wrapper Fivegram Extinction Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `1a62827` on `wave3-m34-transverse`
**Certificate:**
[`certify_mixed_prime_sandwich.rs`](../tools/certify_mixed_prime_sandwich.rs)

## Verdict

No common context wraps any of the `23` Cayley–Hamilton pump schemas or the explicit odd kernel
family into a physical reduced fork. For every pump depth, relation orientation, and words
`P,Q`, the simultaneous factorizations

```text
yzxyx=P·Lₖ·Q,       xzyxy=P·Rₖ·Q
```

are impossible. `P` and `Q` may be empty, arbitrarily long, and chosen separately for each pump
depth and proposed witness. The result closes the complete one-context hull of all `24`
currently explicit infinite relations.

The claim does not cover a multi-window derivation using several kernel relations, a new affine-
kernel relation, or a compiler interface whose terminal equality does not expose one contiguous
common-context relation pair.

## Wrapper Boundaries

For the overlapping factor-count vector `Φᵣ`, internal factors of the common `P` and `Q` cancel.
The discrepancy

```text
Φᵣ(P·Lₖ·Q)−Φᵣ(P·Rₖ·Q)
```

depends only on `suffixᵣ₋₁(P)` and `prefixᵣ₋₁(Q)`. Every possible one-sided boundary is therefore
represented by one word of length at most `r−1`. The complete wrapper catalogues have

```text
r=3: (1+2+4)²     = 49 cells,
r=4: (1+2+4+8)²   = 225 cells,
r=5: (1+2+4+8+16)² = 961 cells.
```

The two-letter pump locality from `G3-S30` is unchanged by arbitrary outer contexts. Trigrams
have the depth classes `k=0` and `k≥1`; fourgrams and fivegrams have `k=0`, `k=1`, and `k≥2`.
The certificate checks the common periodic increment on both relation sides at all three factor
lengths. This is an all-depth lasso, not a replay cutoff.

## Staged Filter

The radius-three pass checks

```text
24 families · 2 depth classes · 49 wrapper cells = 2,352 forward cells.
```

Exactly `72` survive. Relation reversal doubles the audited population to `4,704` cells and the
survivors to `144`. The forward survivor histogram is

```text
l32-02: 9    l32-04: 42    l32-05: 2
l32-08: 3    l32-09: 14    l32-13: 2.
```

Refining only those cells to radius four checks `1,092` oriented cells. Sixty-two survive:
thirty-one forward cells and their negatives. The forward population consists of one `l32-02`
cell and thirty `l32-04` cells. These occupy eighteen distinct oriented fourgram targets.

## Conditional Fivegrams

A full fivegram physical catalogue would enumerate `510³` representative triples. Conditional
refinement is exact and smaller. Every radius-five physical representative projects to one of
the `126` radius-four representatives. Exact enumeration finds `698` radius-four physical
triples in the eighteen surviving target fibres. Lifting only those triples through every
radius-five representative preimage checks `33,218` triples and produces `2,484` distinct
conditional fivegram discrepancies.

The sixty-two radius-four wrapper cells refine to `414` oriented radius-five cells with `148`
distinct parent/target pairs. None occurs in its corresponding conditional physical fibre. The
certificate also checks that every lifted radius-five triple projects back to its claimed
radius-four target and that candidate and physical fibres are closed under simultaneous
negation. The sorted conditional catalogue has FNV-1a fingerprint

```text
545b855825828176.
```

This conditional construction is exhaustive: any physical fivegram witness would project to
one of the enumerated radius-four triples and then occur among its enumerated radius-five
preimages.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Arbitrary common contexts reduce to finite one-sided boundary words | promoted | exact factor-boundary cancellation |
| All pump depths reduce to two trigram and three fourgram/fivegram classes | promoted | exact periodic-factor lasso |
| Any explicit infinite relation has a physical common-context fork | rejected | complete conditional fivegram certificate |
| Reversing the relation or varying context lengths with depth repairs it | rejected | explicit oriented cells; boundary enumeration is length-free |
| Every one-context use of the `24` explicit families is impossible | promoted | direct composition of the factor equation |
| Every multi-window quotient derivation localizes to one relation | open | outside the one-context hypothesis |
| Every affine-kernel relation is covered | open | the explicit corpus is not the full kernel |
| `M₃(4)` follows | rejected | multi-window/new-kernel geometry and the terminal converse remain |

## Master Delta

```text
DEAD: every one-context fork using any of the 24 explicit infinite kernel families.
LIVE: multi-window quotient derivations; new affine-kernel relations; nonlocal terminal routing;
      arbitrary-word terminal converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The Rust certificate is formatted, compiled with warnings denied, and run against the canonical
pump-family manifest. Python lint, formatting, and type checks pass for the manifest emitter.
The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, Rust LSP,
forbidden-aperture scan, and source scour pass.
