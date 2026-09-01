# M₃(2) ReturnSquare Terminal-Budget Audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Claim

Fix `q≥4` and the pure-denominator parameter `c=−1/B`, with `B≥2`. If a bridge zero has word

```text
head :: (properTail ++ [last]),       τ=q^(last+1),
```

then

```text
τ(q^(head+1)+Σ_wait∈properTail(q^(wait+1)−1))<B.           (1)
```

Consequently every `B+q≤2q²` is mortal exactly when `B=q^(head+1)` for some natural `head`.

## Terminal Contraction

For the pure-denominator inverse

```text
P_t(s)=B(st−1)/(st+(B−1)t²−B),
```

the terminal input satisfies `P_t(B)<B/t` whenever `4≤t<B`. After clearing the two positive
denominators, the strict gap is

```text
B(B−t)(t−1)>0.
```

The tail-scale bound from `R32-S54` supplies `t<B` for every bridge zero.

## Remaining Tail

Inverse execution composes from the right. Once the terminal letter is removed, the predecessor
run of `properTail` starts at `P_τ(B)` and ends exactly at `q^(head+1)`. Applying the additive
descent theorem to this shorter run gives

```text
q^(head+1)+Σ_properTail(q^(wait+1)−1)≤P_τ(B)<B/τ,
```

which is (1). No valuation or cancellation assumption enters this argument.

## Shallow Classification

The existing two-return square cage says a nonresonant bridge zero has at least three positive
returns. Hence `properTail` is nonempty. Every scale is at least `q`, so (1) implies

```text
q(2q−1)<B,       or equivalently       2q²<B+q.
```

This contradicts `B+q≤2q²`. The only surviving bridge is a singleton, whose exact closed form
forces `B=q^(head+1)`. Conversely that singleton always vanishes. The physical bridge
equivalence transfers this statement to mortality.

## Boundary

The additive cost alone suggested the first three-return floor `3q−2`. It is not sharp. The
terminal contraction moves the proved resonance-only boundary to `2q²−q`, equal to `28` at
`q=4`, `66` at `q=6`, and `190` at `q=10`.

This remains a chamber theorem, not the full composite-base resonance classification. Larger
denominators remain governed by the finite `R32-S55` certificate.

## Evidence

The formal owner is
[`ReturnSquareShallowDenominator.lean`](../MatrixMortality/ReturnSquareShallowDenominator.lean).
The focused module build, umbrella import, transitive axiom inspection, forbidden-aperture scan,
and whitespace gate passed at the recorded commit. The repository-wide linter remains blocked
only by the pre-existing missing docstrings on the three projections of
`CubicReturn.NonPure.CubicDefectState`; this module emits no compiler or syntax-linter warning.
