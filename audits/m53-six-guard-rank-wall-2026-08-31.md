# Six-Guard Parser Rank Wall

**Date:** 2026-08-31
**Target:** the `MM-O21` guarded changed-series candidate for `M₅(3)`
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every exact realization of the six-guard series needs at least seven states on a
source whose original series has a zero

This result closes one construction. It does not prove `M₅(3)` decidable or undecidable and does
not constrain arbitrary series which preserve only zero existence.

## Witness-Dependent Section

Let `f : Σ* → ℚ`, choose distinct letters `g,s`, and suppose `f(w₀)=0`. The six-guard transform
is

```text
fᴳ(g⁶sw)=f(w),       fᴳ(u)=1 otherwise.
```

For `i,j∈{0,…,6}`, set

```text
pᵢ=gⁱ,               qⱼ=g^(6−j)sw₀.
```

Then `pᵢqⱼ` contains `i+6−j` guards before its separator. If `i=j`, decoding succeeds and its
coefficient is `f(w₀)=0`. If `i<j`, the separator arrives before all six guards have been read.
If `i>j`, the decoder expects the separator while the next letter is `g`; distinctness of `g`
and `s` makes that test fail. Both off-diagonal cases have coefficient one. Thus the selected
Hankel section is

```text
Hᵢⱼ = 0 if i=j, and 1 otherwise;       H=J₇-I₇.       (1)
```

The words in (1) are not a source-independent bounded probe set: every suffix contains the
potentially unbounded witness `w₀`.

## Nonsingularity

For the constant-one matrix `J₇`, direct multiplication gives `J₇²=7J₇`. Hence

```text
(J₇-I₇)((1/6)J₇-I₇)=I₇.                              (2)
```

Equation (2) proves `det H≠0`. If an `n`-state rational linear representation agrees with `fᴳ`
on every word, its finite Hankel section factors through the `n`-dimensional state space.
Therefore (1) and (2) imply `n≥7`.

This argument uses arbitrary-word exactness only once: it instantiates the representation on
the witness-dependent words `pᵢqⱼ`. It does not infer coefficients from existential equivalence.

## Forced-Rule Consequence

For positive deletion width, a Neary terminal match is equivalent to a zero of the forced-`R_c`
derivative. Applying the preceding theorem with `g=toggle`, `s=data b`, and the resulting zero
witness proves:

```text
source has a terminal match
  → every exact rational realization of its six-guard changed series has at least seven states.
```

The `MM-O21` series is therefore not a five-state scalar compiler on any yes-source. Singular
controls do not help; the proof assumes only a wordwise exact representation.

## Boundary

The theorem does not say that every sourcewise zero-equivalent changed series has rank at least
seven. It does not rule out a transform which merges guard progress algebraically, changes
nonzero coefficients, or encodes the witness without the literal guard language. It also makes
no assertion about the guarded series on a no-source.

`MM-O21` remains the correct logical boundary: existential equivalence alone determines no
finite coefficient section. `MM-O22` adds an architecture-specific arbitrary-word no-go by
using a zero witness supplied by the yes-source and exactness of the proposed realization.

## Formal Artifact

[`MatrixMortality/ExistentialProbeBarrier.lean`](../MatrixMortality/ExistentialProbeBarrier.lean)
checks the guard-progress Hankel identity, the explicit inverse, the seven-state exact lower
bound, and the forced-rule terminal specialization. The principal declarations are
`guardedSeries_sixGuard_hankel_eq`, `sixGuardHankel_det_ne_zero`,
`guardedSeries_sixGuard_exact_state_lower_bound`, and
`existentialGuardedForcedRuleC_seven_le_card_of_terminal_match`.
