# M₃(2) Jacobi Schedule-Incidence Audit

Date: 2026-08-11

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The split counter lane requires one fixed rational guard whose deterministic reset orbit is
aperiodic, has unbounded reduced denominators, and perpetually finances its primitive
cancellations through sparse, microscopic, doubly order-broken factors of `pᵃ−1`. Prescribing
an attractive wait schedule is insufficient: the schedule must arise from the fixed rational
reset under one fixed coefficient tuple.

The report did not construct that orbit. It instead identifies its exact schedule-incidence
condition and excludes two finite descriptions of the missing history. Formalization retains
only the native Jacobi coordinate and its exact consecutive-step law; the infinite p-adic
completion and height consequences are independently audited here.

## Native Jacobi Coordinate

For consecutive primitive endpoint reductions

```text
(rᵢ,tᵢ) --(qᵢ=p^aⁱ,hᵢ)--> (rᵢ₊₁,tᵢ₊₁),
```

put

```text
τᵢ = L tᵢ/(hᵢtᵢ₊₁).
```

The primitive endpoint equations give

```text
rᵢ/(Ltᵢ)=qᵢ−1+qᵢˢ/τᵢ
```

and the exact shell transition

```text
qᵢ₊₁+qᵢ₊₁ˢ/τᵢ₊₁
  = A/L + (D/L)(qᵢˢ+(qᵢ−1)τᵢ).                 (1)
```

Lean proves (1) directly from two `PrimitiveEndpointReduction`s in
`PrimitiveEndpointReduction.jacobiTail_transition`. The definition `jacobiTail` is a quotient
of adjacent endpoint data, not a new dynamical register.

Normalize by `βᵢ=(qᵢ−1)τᵢ`. Solving (1) backward gives

```text
βᵢ = −A/D−qᵢˢ+(L/D)qᵢ₊₁
      +(L/D)qᵢ₊₁ˢ(qᵢ₊₁−1)/βᵢ₊₁.              (2)
```

The backward map `𝓕ᵢ` in (2) satisfies

```text
𝓕ᵢ(x)−𝓕ᵢ(y)
  = −(L/D)qᵢ₊₁ˢ(qᵢ₊₁−1)(x−y)/(xy).           (3)
```

Lean checks (3) as `jacobiBackward_sub`. Under the guard hypotheses, `A,D,L,x,y` are p-adic
units while `qᵢ₊₁−1` is a unit, so

```text
vₚ(𝓕ᵢ(x)−𝓕ᵢ(y))=s aᵢ₊₁+vₚ(x−y).
```

## Unique Tail And Reset Incidence

Fix any infinite positive wait schedule. Starting at an arbitrary p-adic unit at level `N` and
iterating (2) backward produces a Cauchy sequence: changing the terminal unit or extending the
truncation changes `βᵢ` by valuation at least

```text
s∑_{j=i+1}^N aⱼ.
```

Completeness of `ℚₚ` therefore gives one compatible p-adic unit tail `𝔅ᵢ`; (3) proves uniqueness.
The backward maps preserve units because their constant term is `−A/D` and every other term has
positive valuation.

The reset state is compatible exactly when

```text
𝔅₀ = Lq₀ˢ(q₀−1)/(A+D−Lq₀).                 (4)
```

If (4) holds, `β₀` is rational and the forward rearrangement of (2) makes every later `βᵢ`
rational. Uniqueness identifies this rational sequence with the p-adic unit tail, and the
checked integral lift supplies the corresponding primitive rational guard orbit. Conversely,
every reset-started orbit satisfies (4). Thus a schedule-first counterorbit is precisely an
aperiodic schedule for which one explicit p-adic continued fraction equals the rational reset
value. No such schedule or coefficient tuple was produced.

## Handoff Height

Put

```text
αᵢ=βᵢ/(qᵢ₊₁−1).
```

Writing `Q=qᵢ₊₁` and `Q′=qᵢ₊₂`, (2) becomes

```text
LQˢ(Q−1)/(αᵢ₊₁(Q′−1))
  = A−Dαᵢ+(Dαᵢ−L)Q+Dqᵢˢ.                   (5)
```

All terms other than `A−Dαᵢ` have valuation at least
`min(aᵢ₊₁,saᵢ)`, so

```text
vₚ(A−Dαᵢ) ≥ min(aᵢ₊₁,saᵢ).                 (6)
```

Equality `αᵢ=A/D` is impossible: unequal adjacent exponents leave the smaller of
`aᵢ₊₁,saᵢ`, while equality reduces the right side of (5) to
`(A+D−L)Q`, whose valuation is `aᵢ₊₁<s aᵢ₊₁`. If `αᵢ=mᵢ/nᵢ` is reduced, both integers are
p-units and (6) yields

```text
H(αᵢ) ≥ p^min(aᵢ₊₁,saᵢ)/(|A|+|D|).         (7)
```

If the handoff alphabet were finite, an unbounded source-wait subsequence forces an adjacent
unbounded target-wait subsequence by (5) at the real place; (7) then contradicts finite height.
The waits are therefore bounded. The state formula

```text
zᵢ=qᵢ+qᵢˢ(qᵢ−1)/(αᵢ(qᵢ₊₁−1))
```

then has finite image, and determinism forces eventual periodicity. Every aperiodic reset orbit
uses an infinite, unbounded-height handoff alphabet.

## One Rational Chart

Suppose infinitely many transitions lie on one fixed rational ready-tail chart `T(X)` and both
source and target waits tend to infinity. Unit values at prime powers force numerator and
denominator order zero at `X=0`. For

```text
Z(X)=A/L+(D/L)(Xˢ+(X−1)T(X)),
```

target readiness gives `vₚ(Z(pᵃ))=b`. The zero order of `Z` therefore forces

```text
b=ma+c,      pᵇ=pᶜ(pᵃ)ᵐ
```

eventually. The allegedly arbitrary successor schedule has become an affine monomial rail.
The checked polynomial divisibility argument in `ReturnGuardRail.lean` then forces `m=1`, equal
numerator and denominator degrees, and

```text
A/L=(pᶜ)^(s+deg numerator).
```

Since both `A/L` and `A/L−1` are p-adic units, this is impossible. An aperiodic orbit cannot be
confined eventually to one rational chart. This strengthens the finite-atlas obstruction by
removing its assumed affine successor law in the one-chart case; the final polynomial step is
the existing formalized rail theorem rather than a duplicate API.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| exact Jacobi shell transition and backward difference | promotion | kernel checked in `ReturnGuardContinued.lean` |
| every schedule has one compatible p-adic ready tail | promotion | audited contraction and completeness argument |
| reset realization is the scalar continued-fraction identity (4) | promotion | exact two-way rational reconstruction |
| finite handoff alphabet supports an aperiodic orbit | rejected | height payment forces bounded waits and periodicity |
| one fixed rational chart can carry arbitrary successor scheduling | rejected | readiness forces the already impossible monomial rail |
| packet birth-storage table | restatement | existing moving-prime allocation and reverse-persistence calculus |
| fixed rational aperiodic counterorbit or undecidability reduction | open | no coefficients or simulation were obtained |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
REMOVED: schedule-first construction; finite handoff controllers; one fixed rational ready-tail chart
EXACT COUNTER THROAT: an aperiodic schedule satisfying the rational reset incidence (4) through unbounded-height, history-dependent handoffs
DECISION DUAL: exclude precisely those moving Jacobi tails by a reset-anchored first-hit certificate
```
