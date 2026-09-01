# M₃(4) Explicit Sandwich Boundary Extinction Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `c038d3b` on `wave3-m34-transverse`
**Certificate:**
[`certify_mixed_prime_sandwich.rs`](../tools/certify_mixed_prime_sandwich.rs)

## Verdict

None of the `23` Cayley–Hamilton pump schemas or the explicit odd mixed-prime kernel family can
realize the central sandwich

```text
yzxyx=W·Lₖ·W,       xzyxy=W·Rₖ·W
```

for an aligned address `W∈{DT,TD}*`. This holds at every pump depth and in both orientations of
each relation. Combined with `G3-S24`–`S26` on the two endpoint placements and the `G3-S29`
two-cut trichotomy, every uniform same-address double insertion in every currently explicit
infinite kernel family is impossible.

The claim is family-specific. It does not exclude a new kernel relation, two different address
segments, a reversed or state-dependent second address, address-dependent cuts, a restricted
producer, or a separate two-offset terminal channel.

## Boundary Completeness

Let `Φᵣ(w)` count the overlapping length-`r` factors of `w` in lexicographic `D<T` order. For
`r≥2`, put

```text
Rᵣ = ⋃₁≤ℓ≤2r−3 {D,T}^ℓ  ∪
     {pq : p,q∈{D,T}^{r−1}}.
```

Every nonempty word shorter than `2(r−1)` occurs verbatim. A longer word is replaced by its
length-`r−1` prefix followed by its length-`r−1` suffix. Any artificial factor at the new middle
seam is internal to one macro and cancels because `x` and `y` occur twice on both physical sides
and `z` occurs once. Every original crossing factor is preserved. Hence

```text
Bᵣ={Φᵣ(yzxyx)−Φᵣ(xzyxy) : x,y,z∈Rᵣ}
```

is the complete physical discrepancy catalogue for nonempty `x,y,z`, not a word-length cutoff.
Endpoint exactness supplies that nonemptiness through
`GuardedMixedPrimeReducedKernel.bcbc_macro_words_ne_nil`.

The exact catalogues are

| `r` | representatives | triples | distinct discrepancies |
| ---: | ---: | ---: | ---: |
| `3` | `30` | `27,000` | `1,243` |
| `4` | `126` | `2,000,376` | `93,463` |

Swapping `x` and `y` negates the discrepancy, so both catalogues are negation-closed. The
certificate also checks every reverse target explicitly.

## Address And Pump Locality

In `Φᵣ(WLₖW)−Φᵣ(WRₖW)`, internal factors of both copies of `W` cancel. Only
`suffixᵣ₋₁(W)·Lₖ·prefixᵣ₋₁(W)` remains. Aligned addresses have exactly five radius-two boundary
pairs: the empty address and the four choices of first and last macro. Radius three has exactly
nineteen: the empty address, the two one-macro words, and the sixteen independent pairs of the
first and last two macros. Depth four realizes all sixteen long cells.

Every family has the form

```text
Lₖ=A·Sᵏ·C,       Rₖ=B·Sᵏ·E,       S∈{DT,TD}.
```

Once `2k≥r−1`, no length-`r` factor spans both pump seams. The pump prefix and suffix are fixed,
and adding one copy of `S` contributes the same two periodic internal factors to both sides.
Thus the sandwich discrepancy is constant for every later `k`. For trigrams, `k=0` and `k≥1`
are the complete depth classes. For fourgrams, `k≥2` is stable; the only surviving family at
`k≥1` has equal targets already at `k=0,1,2`.

## Two-Stage Extinction

The trigram pass checks `24·2·5=240` forward cells. Exactly three survive:

```text
l32-02, k=0,  suffix(W)=DT, prefix(W)=TD:
  (-1,1,0,0,1,-1,0,0)

l32-04, k=0 and k≥1, suffix(W)=DT, prefix(W)=DT:
  (-1,0,2,-1,0,1,-1,0).
```

Radius-three boundary refinement gives four cells for `l32-02` and five for `l32-04`. The latter
five represent both its preperiod and stable trigram classes, so there are fourteen forward
logical cells and twenty-eight after relation reversal. Every fourgram target misses `B₄`.

As an independent conditional audit, among the `R₄³` physical triples the two orientations of
the `l32-02` trigram have `1,232` witnesses each and `144` distinct fourgram refinements; the two
orientations of `l32-04` have `1,152` witnesses each and `144` refinements. None equals the
corresponding sandwich target. The sorted-catalogue FNV-1a fingerprints are

```text
B₃  2db1b99ff0292296
B₄  c6444bcfd9d055b4
```

The certificate consumes the canonical `23`-family manifest emitted by
`certify_mixed_prime_pump_families.py`; it does not duplicate that corpus.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| `Rᵣ` represents every nonempty physical macro at factor length `r` | promoted | exact boundary-factor argument |
| The aligned address has only `5` trigram and `19` fourgram boundary cells | promoted | exact first/last-macro classification |
| All pump depths reduce to the stated finite cells | promoted | exact two-letter factor-locality argument |
| Any of the `24` explicit families realizes the central sandwich | rejected | exhaustive `B₃/B₄` certificate |
| Reversing a relation repairs the mismatch | rejected | negation closure and explicit reverse checks |
| Any explicit family realizes a uniform same-address double insertion | rejected | this result, `G3-S24`–`S26`, and `G3-S29` |
| Any mixed-prime kernel relation admits such a sandwich | open | outside the explicit family corpus |
| `M₃(4)` follows | rejected | new geometry, nonuniform production, routing, and converse remain |

## Master Delta

```text
DEAD: every uniform same-address double insertion in all 24 explicit infinite kernel families.
LIVE: new kernel geometry; different/reversed/stateful addresses; restricted production;
      separate two-offset routing; arbitrary-word terminal converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The Rust certificate is formatted, compiled with warnings denied, and run through the canonical
pump-family manifest. Python lint, formatting, and type checks pass for the manifest emitter.
The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, forbidden-
aperture scan, and source scour remain unchanged and pass.
