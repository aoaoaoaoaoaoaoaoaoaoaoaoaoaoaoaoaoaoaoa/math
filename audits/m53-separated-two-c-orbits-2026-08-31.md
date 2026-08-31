# Separated Two-C Orbit Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

The coupled width-three source family contains an infinite, Lean-checked nonhalting stratum with
two genuinely separated `c` letters. For every positive `n` congruent to zero or one modulo
three, the body

```text
qₙ = bb c bⁿ c bⁿ
```

is admissible and its prescribed input `qₙ.drop 2 · b` enters an explicit periodic orbit. This
sharpens the source boundary but does not classify the separated family or prove universality.

## Exact Macro Orbit

Put

```text
Cₙ = c b^(2n+2),
Dₙ = b^(2n+2) c bⁿ c b^(n+1).
```

One `cbb` stroke gives `Cₙ→Dₙ`. The return depends only on `n mod 3`.

For `n=3(k+1)`, consume

```text
(bbb)^(2k+2), bbc, (bbb)^(k+1).
```

This prefix leaves `c b^(3k+4)`. All `3k+4` heads are `b`, so the produced suffix is
`b^(3k+4)` and the queue returns to `c b^(6k+8)=Cₙ`.

For `n=3k+1`, consume

```text
(bbb)^(2k+1), bcb, (bbb)^k.
```

This prefix leaves `c b^(3k+2)`. Its `3k+2` `b`-headed strokes emit the same unary suffix,
returning to `c b^(6k+4)=Cₙ`. In both cases the complete cycle has exactly `n+2` steps.

## Coupled Entry

For the positive zero residue, write `n=3(k+1)`. The initial `cbb` stroke reaches a bridge whose
remaining `b`-headed history is

```text
(bbb)^k, bcb, (bbb)^(k+1), bbc, (bbb)^(k+1).
```

It leaves `c b^(3k+4)` and emits `b^(3k+4)`, hence reaches `Cₙ`.

For positive one residue above the base case, write `n=3(k+1)+1`. The corresponding history is

```text
(bbb)^k, bbc, (bbb)^(k+2), bcb, (bbb)^(k+1).
```

It leaves and emits `b^(3k+5)` after the leading `c`. At `n=1`, the first input stroke is `cbc`
rather than `cbb`; it reaches `D₁` directly, and the general one-residue return reaches `C₁`.

## Checked Boundary

[`MatrixMortality/SeparatedTwoCOrbit.lean`](../MatrixMortality/SeparatedTwoCOrbit.lean) proves:

- `separatedBody_length` and `separatedBody_admissible`: `|qₙ|=2n+4`, with the required even
  length;
- `zeroResidue_initial_reaches_cycle` and `oneResidue_initial_reaches_cycle`: exact coupled
  entry reachability;
- `cycleQueue_step`, `zeroResidue_expanded_reaches_cycle`, and
  `oneResidue_expanded_reaches_cycle`: the exact `Cₙ→Dₙ→Cₙ` macro;
- `zeroResidue_cycle` and `oneResidue_cycle`: exact cycle length `n+2`;
- `separated_not_tagHaltsFrom`: nonhalting for `n>0` and `n mod 3≠2`.

The theorem makes no claim about `n≡2 (mod 3)`, unequal separated runs, more than two `c`
letters, or undecidability of any fixed-width source class.
