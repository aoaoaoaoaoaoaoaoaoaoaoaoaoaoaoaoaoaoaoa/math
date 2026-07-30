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
the arithmetic reachability of its nested equal-depth resonance.

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

## Checked Shift Factorization

In the coordinate `x=z/(z−1)`, Lean verifies

```text
Dₐ(x) = (pᵃ+(1−pᵃ)x)/pˢᵃ,
K(w)  = (αw+δ)/((α−1)w+δ),
x'    = K(Dₐ(x)).
```

The theorem retains the input target and pole exclusions. Rational division is total, so the
algebraic equality also survives a terminal output; no affine-chart assertion is made there.
Readiness is equivalent to `Dₐ(x)` being a p-adic unit.

On the branch cylinder

```text
Φₐ(v)=(pˢᵃv−δ)/(α−pᵃ),
```

the reciprocal residual obeys the exact affine law

```text
1/Rₐ(Φₐ(v))
  = [δ(1−pᵃ)/(α−pᵃ)]/v
    + [(α−1)pˢᵃ/(α−pᵃ)].
```

Every denominator used in the affine interpretation is explicit in the theorem hypotheses.

## Checked Decoded Address Grammar

Formalization exposed a more canonical coordinate than the shifted affine chart:

```text
w=(ρ−α)/(z−α),              z=α+(ρ−α)/w.
```

It sends reset to `1` and the terminal point to

```text
τ=−(ρ−α)/(α−1).
```

For every positive wait `a`, Lean proves that the exact legal domain is the rational part of one
p-adic sphere around

```text
βₐ=−(ρ−α)/(α−pᵃ),
```

at valuation depth `sa`. The inverse branch maps every rational p-adic unit into this sphere,
the residual step maps it back, and the two maps are mutual inverses on their stated domains.
The spheres are pairwise disjoint.

Transporting `LegalStep` through this coordinate and inducting over transitive closures gives

```text
physical mortality
  ↔ ∃ nonempty positive list (a₀,…,aₙ),
      1=gₐ₀(⋯gₐₙ(τ)⋯).
```

This theorem inherits the complete arbitrary-physical-word converse; it is not merely a
re-encoding of intended legal runs. Distinct positive branches have no common finite
cross-multiplied fixed point.

The report described a full shift over `ℚₚ`. The checked theorem deliberately stops at exact
rational spheres and inverse addresses. No topological conjugacy or completion theorem has been
claimed.

## Checked Resonance Localization

Let `u=α/δ` and write a unit tail as `X=u+pⁿY`, with `Y` a unit. The three terms of the legal
output have valuations `a`, `sa`, and `n`. Lean proves:

```text
n<a  ⇒ any next ready wait equals n;
n>a  ⇒ the output is not ready and every subsequent positive step is trapped;
n=a  ⇒ the only possible nondecreasing branch.
```

The exact center `X=u` cannot produce a ready state. Hence every infinite ready chain resonates
at depth `a` arbitrarily far along the chain.

Formalization found one error in the report. If the resonant output is
`p^(a+h)U`, with `U` a unit, readiness at wait `a+h` requires

```text
vₚ(U−1)=(s−1)(a+h),
```

not `(s−1)a+sh`. The reported value exceeds the correct depth by `h`.

An exact rational period-three orbit is now checked at

```text
p=3, s=2, α=−953/2240, ρ=−3/14:
1 ─1→ 5/17 ─2→ 43/283 ─3→ 1.
```

The first two legs are equal-depth resonances; the third is nonresonant descent from wait three
to wait one. This refutes any classification of rational survivors by fixed points and
two-cycles alone. It does not refute eventual periodicity.

## Checked Integral and Cyclotomic Sieve

Writing `α=A/L`, `ρ−α=D/L`, and a decoded rational residual as a primitive pair `m/n`, Lean
checks the exact integral recurrence

```text
pˢᵃm̃=(A−Lpᵃ)m+Dn,
ñ=(A−L)m+Dn
```

and proves that `m̃/ñ` is exactly the decoded residual step.

A generalized determinant theorem shows that any common divisor of the image of a primitive
integer pair under a `2 × 2` integer matrix divides its determinant. For the guard recurrence,
every common reduction factor `g` coprime to `p` therefore satisfies

```text
g∣DL(pᵃ−1).
```

If a prime `ℓ` divides `pᵃ−1`, the reduced output obeys the exact dichotomy

```text
ℓ∣g  or  m′≡n′ (mod ℓ).
```

The second branch is the finite-quotient reset to projective one. The first is the sole local
escape: the cyclotomic prime is swallowed by common cancellation. This is a one-step sieve, not
an effective bound on cancellation histories.

## Checked Rational-Rail Obstruction

For a reduced rational chart `f=P/Q`, an affine wait update
`a↦da+h` becomes `t↦λtᵈ`, with `λ=pʰ`. Infinitely many defined rail samples imply a polynomial
identity. Rather than formalizing the report's algebraic-closure divisor count, the Lean proof
extracts

```text
P(λXᵈ) ∣ Q(X).
```

Degree comparison forces `d=1` and `deg P=deg Q`. Constant and leading coefficients then force

```text
α=λ^(s+deg P).
```

This contradicts `vₚ(α)=0` when `vₚ(λ)≠0`. The formal theorem is stated both for an arbitrary
infinite set of defined rational samples and for infinitely many prime-power samples.

The result excludes one reduced rational chart. The suggested finite-control corollary still
requires a typed theorem that a control cycle composes to the same rail equation; that
compiler-level statement was not promoted.

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

At `p=3`, `s=2`, `ρ=−3/14`, and `α=−953/2240`, the checked decoded period-three cycle above
corresponds to original guarded states

```text
−3/14 ─1→ 117/400 ─2→ 27/28 ─3→ −3/14.
```

## Open Boundary

The sole live constructive question is reachability for the deterministic legal-tail map. A
future proof must either:

1. construct a rational nonperiodic computation inside the nested equal-depth resonance; or
2. prove rational inverse addresses effectively eventually periodic or otherwise decidable,
   most plausibly by bounding cyclotomic common cancellation.

The matrix dimension, generator count, punctuation, rank profile, malformed words, illegal
waits, arbitrary-product converse, generic nonresonant dynamics, and rational affine counter
rails are no longer open in this architecture.
