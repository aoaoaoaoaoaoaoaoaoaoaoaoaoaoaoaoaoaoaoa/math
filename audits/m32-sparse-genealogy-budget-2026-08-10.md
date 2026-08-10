# M₃(2) Sparse-Genealogy Budget Audit

Date: 2026-08-10

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

The split-guard counter route needs one reset-started aperiodic legal orbit with unbounded reduced
denominators and recurrent activation of moving factors of `pᵃ−1`. The attack attempted to start
such an orbit from the checked order-breaking bridge and derived a global endpoint potential when
the construction failed.

Formalization resolves both parts more sharply. The proposed fixed tuple has a short forced
continuation and then enters the trap, so it is not an unproved infinite candidate. The potential
is an endpoint-adapted coordinate form of the checked content-weighted height calculus; its
iteration yields useful asymptotic restrictions without earning a second Lean API.

## The Candidate Dies

The proposed parameters are

```text
(p,s,A,D,L)=(3,2,249398,1,1).
```

The existing theorem `orderBreaker_shatters_resetBall` checks the first two transitions, the
order-four prime `5`, the lack of `5`-cancellation, and the denominator jump from `19` to
`270178`. Pro stopped at the next ready state. Continuing the deterministic orbit gives

```text
249399
  → 4863261/19
  → 67384284465/270178
  → 1867323343063569/7487052659
  → 25873217288233051767/103738937883644
  → 716987098491311042884493/2874767341268822315.
```

The forced waits are `[4,1,1,1,1]`. The first five sources satisfy the exact depth-two readiness
equation. The final rational is a nonterminal 3-adic unit, hence belongs to the forward-invariant
trap and admits no legal continuation. Lean checks every new transition, both intermediate
readiness statements, and the final valuation in
`ReturnGuard.Examples.orderBreaker_candidate_enters_trap` from
[`ReturnGuardCounterorbit.lean`](../MatrixMortality/ReturnGuardCounterorbit.lean).

The bridge remains a valid counterexample to denominator descent and to preservation of a strict
auxiliary-prime reset ball. It is rejected as the seed of an infinite activation genealogy.

## Endpoint-Adapted Potential

For a live primitive endpoint pair `(rₙ,tₙ)`, signed forward content `hₙ`, and
`qₙ=p^aⁿ`, put

```text
uₙ=rₙ−(A−L)tₙ,
Ψₙ=max(|D||tₙ|,|uₙ|),
Γ=|A|+|D|+|L|.
```

At depth two the exact endpoint recurrence is

```text
qₙ²hₙtₙ₊₁ = uₙ+(A−Lqₙ)tₙ,
hₙuₙ₊₁    = D(uₙ+(A−L)tₙ).
```

Triangle inequalities, `qₙ≥1`, and `tₙ₊₁≠0` give

```text
|hₙ|Ψₙ₊₁ ≤ ΓΨₙ,
qₙ|D||hₙ| ≤ ΓΨₙ.                                    (1)
```

This is a fixed invertible endpoint coordinate and max norm, not a new dynamical register. The
checked theorems `integralStep_content_mul_height_le` and `integralStep_wait_content_le` already
own the native content-height law with the same coefficient envelope. The displayed form is
retained only because it makes the global genealogy consequences transparent.

At reset, `Ψ₀=|D|`. With `P_N=∏_{n<N}|hₙ|`, iteration of (1) gives

```text
P_N Ψ_N ≤ |D|Γᴺ,
p^aⁿ P_{n+1} ≤ Γⁿ⁺¹.                                 (2)
```

If `Q_N` is the reduced denominator of
`1+r_N/(Lt_N)`, primitivity gives

```text
Q_N=|L||t_N|/gcd(|L|,|r_N|),
Q_N P_N ≤ |L|Γᴺ.                                      (3)
```

All multiplicities survive in these products.

## Genealogy Consequences

Suppose activation `i` occurs at time `n_i` with a prime power `d_i=ℓ_i^e_i` dividing the
forward content. Equations (2)–(3) imply

```text
Q_N ∏_{n_i<N} d_i ≤ |L|Γᴺ,
p^ord_{d_i}(p) ∏_{j≤i} d_j ≤ Γ^(n_i+1).               (4)
```

For distinct fresh primes, their product is at least `(K_N+1)!`; hence the number born before
time `N` satisfies

```text
K_N=O(N/log N).
```

Positive-density fresh-prime simulation is impossible, although a computable superlinear
slowdown is not an undecidability obstruction.

If an infinite orbit is aperiodic, every activated packet is microscopic:

```text
d_i/Ψ_{n_i} → 0.                                      (5)
```

Otherwise `d_i≥εΨ_{n_i}` infinitely often, and (1) puts infinitely many successor pairs in one
bounded integer box. A repeated rational state makes the deterministic orbit eventually
periodic. Similarly, recovering the pre-activation height requires

```text
m−n_i ≥ ⌈log_Γ d_i⌉.                                  (6)
```

Finally, if two consecutive contents equal their entire source endpoint numerators in absolute
value, substitution into the two endpoint equations gives, for the second wait power `q`,

```text
|A−L|q² ≤ |A−L|+|L|(1+|D|)(q−1).
```

Thus consecutive full-numerator handoffs have a coefficient-effective wait bound. Any surviving
counterorbit must leave large cofactors or insert changing bridges.

## Adjudication

| Claim | Class | Judgment |
| --- | --- | --- |
| the displayed bridge starts an infinite genealogy | rejected | exact continuation reaches a nonterminal 3-adic unit after forced waits `[4,1,1,1,1]` |
| the bridge breaks order and amplifies denominator height without activating `5` | restatement | already checked by `orderBreaker_shatters_resetBall` |
| endpoint potential and one-step inequalities | restatement | endpoint-adapted form of the checked `R32-S29` content-height calculus |
| global content, denominator, and wait budgets | promotion | independently derived multiplicity-sensitive corollaries of the checked one-step law |
| fresh-prime sparsity, microscopic allocation, and recovery delay | promotion | exact asymptotic consequences, conditional on the stated activation and aperiodicity hypotheses |
| consecutive full-numerator handoff bound | promotion | direct two-step endpoint calculation |
| every infinite genealogy is impossible | open | sparse microscopic doubly order-broken allocations remain consistent with all bounds |

## Wound

```text
MASTER VERDICT: M₃(2) remains open
KILLED: the explicit (3,2,249398,1,1) counterorbit candidate; dense or macroscopic prime-register designs
REMAINS: a reset-started aperiodic orbit with unbounded denominators and a sparse, microscopic, doubly order-broken moving-prime genealogy
DECISION DUAL: an effective reset-anchored recurrence-or-escape certificate for exactly that residue
```
