# Sourcewise-Existential Probe Blindness

**Date:** 2026-08-31
**Target:** the weak `M₅(3)` scalar and bordered-companion interfaces
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** existential zero equivalence has no finite probe-rank consequence; a complete
computable probe cutoff is impossible

Nothing below proves `M₅(3)` decidable or undecidable, and the constructed changed series is not
a five-state linear representation.

## Correct Quantifiers

The master reduction needs only

```text
source has a terminal match  ↔  target series has some nonempty zero.
```

It does not identify the target's coefficient at any named word. In particular, it does not say
that a source terminal word remains a zero at the same physical spelling, or that any prescribed
finite family contains a witness.

## Guard Evasion

Let `f : Σ* → R`, choose two letters `g,s∈Σ`, and fix a horizon `N`. Define

```text
fᴳ(gᴺsw)=f(w),       fᴳ(u)=1 otherwise.                 (1)
```

The prefix decoder is total and exact on guarded words. Every copied witness is nonempty, and a
word outside the guarded image has coefficient one. Over a nontrivial semiring,

```text
fᴳ has a nonempty zero  ↔  f has a zero.                 (2)
```

Successful decoding requires word length at least `N+1`. Hence every word of length at most `N`
has value one. Given arbitrary finite prefix and suffix families, choose `N` above every
concatenated length. Their entire Hankel section for `fᴳ` is then the constant-one matrix.

This is stronger than merely making one old determinant vanish: the sourcewise existential
criterion does not entail any bounded coefficient or zero-incidence pattern at all.

## Forced-Rule Specialization

For deletion width `β>0`, every Neary terminal-match word begins with `R_c`. Conversely, the
paired decoder is surjective on every remaining role tail. Therefore

```text
∃w, h(w)=0  ↔  ∃z, z is a Neary terminal match,
```

where `h(w)` is the semantic forced-`R_c` derivative from `MM-O18`.

Apply (1) with guard letter `t`, separator letter `b`, and `N=6`. The resulting changed series
has a nonempty zero exactly when the source has a terminal match. Every one of the sixteen
inserted-toggle words used by `MM-O18` has length at most six, so every entry of that `4×4`
section is one and its determinant is zero.

Thus the exact companion obstruction is sharp: its finite determinant follows from exact joint
channel realization, not from sourcewise zero existence.

## Bounded Search Wall

The guard transform explains why a fixed probe family cannot work. A separate computability
argument excludes source-dependent finite completeness as well.

Let `test(e,n)` be a primitive-recursive probe predicate and `B(e)` a primitive-recursive
cutoff. Then

```text
P(e) := ∃n < B(e), test(e,n)
```

is computable by bounded search. The universal paired zero predicate is equivalent to mathlib's
halting predicate and is not computable. Therefore `P(e)` cannot agree with universal paired
zero existence for every source code `e`.

Any proposed weak architecture which derives a computable bound on its shortest witness is
therefore dead. This includes a finite probe-rank consumer only if the architecture proves that
its finite probes are complete; a determinant on arbitrary nonwitness words says nothing.

## Remaining Boundary

The word-series transform (1) uses a finite regular guard but no five-state realization is
claimed. Realizing a six-letter horizon naïvely costs additional parser states. It is a logical
countermodel to finite-probe inference, not a candidate reduction.

The live constructive obligation is unchanged: exhibit two `5×5` rational or integer matrices
whose scalar series has the correct sourcewise zero existence, or complete the setter's direct
three-generator mortality converse. A valid no-go must extract an arbitrary-word semantic
consequence from a narrower architecture, such as a computable witness bound, a pumping law, or
a decidable quotient.

## Formal Artifact

[`MatrixMortality/ExistentialProbeBarrier.lean`](../MatrixMortality/ExistentialProbeBarrier.lean)
checks the guard decoder, zero-existence equivalence, finite-Hankel collapse, forced-rule terminal
equivalence, the singular `MM-O18` specialization, bounded-probe computability, and the
contradiction with universal paired zero undecidability.
