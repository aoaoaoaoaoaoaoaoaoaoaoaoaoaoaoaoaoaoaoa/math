# M₃(2) Amalgamated Valuation-Guard Audit

Date: 2026-07-29

## Verdict

The separator-verifier-trap construction survives independent reconstruction and Lean
formalization. The checked theorem is stronger and cleaner than the reported version:

- “odd prime” is not primitive; the exact hypotheses are that `α` and `α−1` are p-adic units;
- every arbitrary physical word is covered in actual matrix multiplication order;
- the ready-cylinder transition graph has a checked explicit inverse branch;
- mortality is equivalent to one deterministic transitive-closure reachability problem.

No `M₃(2)` undecidability or decidability theorem follows. The remaining obligation is entirely
the arithmetic reachability of the guarded tail recurrence.

## Checked Algebra

For prime `p`, depth `s≥2`, center `α`, reset `ρ`, and `δ=ρ−α`, the construction uses

```text
A = diag(1,p⁻¹,p^(s−1)),
B = UV.
```

The return `VAⁿU`, after multiplication by the nonzero scalar `pⁿ`, is

```text
[α+δpˢⁿ    −αpⁿ−δpˢⁿ]
[1                    −pⁿ].
```

Lean proves:

- `B` has rank two when `δ≠0`;
- the zero return is `(ρ,1)ᵀ(1,−1)`;
- its square is `(ρ−1)` times itself;
- every positive return is invertible;
- the exact coefficient Hankel section has rank three;
- the split return normal form reflects all physical zero words to interface products.

The refactor extracted the last statement into
`ReturnFamily.pairGenerator_isMortal_iff_positiveBridge`; ReturnSquare and ReturnConvert now use
the same compiler.

## Checked Projective Guard

`ProjectiveLine.Point ℚ = Option ℚ` presents finite points as `some z` and infinity as `none`.
The action is total at poles and carries the nonzero homogeneous weight discarded by
projectivization. Unit matrix words reach the terminal covector kernel exactly when their total
projective state is `some 1`.

The guard identity is checked without division:

```text
Nₙ(z)−αDₙ(z)=δpˢⁿ(z−1),       Dₙ(z)=z−pⁿ.
```

Under the unit hypotheses and `vₚ(ρ)>0`, Lean proves:

```text
Trap = ℙ¹(ℚ) \ ({z≠0 : vₚ(z)>0} ∪ {1})
Φₙ(Trap) ⊆ Trap
```

for every positive wait. If a live point survives, then

```text
n=vₚ(z),       vₚ(z−pⁿ)=sn.
```

Zero, infinity, negative-valuation points, nonterminal units, wrong waits, shallow carries, and
excessive carries are all treated separately. No affine-chart pole is silently excluded.

## Checked Tail Grammar

Every ready point has a unique unit tail:

```text
E(a,X)=pᵃ+pˢᵃ/X,       vₚ(X)=0.
```

Its legal update is

```text
E(a,X) ↦ α+δ(pˢᵃ+(pᵃ−1)X).
```

For every positive `a,b` and every unit `X′`, the checked `inverseTail` is a unit and maps the
source `a`-cylinder exactly to `E(b,X′)`. The checked `targetTail` is the unique unit payload
that reaches one.

This establishes local symbolic completeness, not universality: one rational tail must satisfy
the whole itinerary.

## Arbitrary-Word Converse

Positive-return labels are indexed from zero but act with waits `n=index+1`. Matrix products act
on columns from right to left, and `guardedOrbit` uses that order definitionally.

For a successful arbitrary word, trap invariance first proves that every suffix state survives.
The suffix state cannot already be terminal, because one further positive return would enter the
trap. It is therefore live, and `live_step_forces_ready` makes the next physical label the
unique legal transition. Induction produces

```text
ReflTransGen LegalStep ρ z.
```

Since `ρ≠1`, a terminal hit yields `TransGen LegalStep ρ 1`. Conversely, every legal path is
reified by prepending its labels to the physical wait word. Hence

```text
physical_isMortal_iff_guardedReachable.
```

This is the central audited theorem.

## Concrete Certificates

At `p=5`, `s=2`, `ρ=30`, and `α=869/28`, the reset is ready and the unique legal wait one reaches
the target. Denominator clearing gives

```text
A = diag(5,1,25),
B =
  [ −28    28    0]
  [−869   869  −29]
  [−841   841  −29],
```

with the checked identity `B²AB²=0`.

At `p=5`, `s=2`, `ρ=5/6`, and `α=2`, the ready reset is a checked nonterminal fixed point.

## Open Boundary

The sole live constructive question is reachability for the deterministic legal-tail map. A
future proof must either:

1. compile a universal deterministic computation into its rational tail itinerary; or
2. derive a global p-adic, height, continued-fraction, or finite-nucleus invariant deciding it.

The matrix dimension, generator count, punctuation, rank profile, malformed words, illegal
waits, and arbitrary-product converse are no longer open in this architecture.
