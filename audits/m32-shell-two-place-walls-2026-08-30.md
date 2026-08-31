# Two-Place Walls in the Mixed-Prime Shell

Date: 2026-08-30

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Claim

The normalized benchmark transition is

```text
T_m(u) = (q_m u + 1)/5,       q_m = 3(2/3)^m.
```

Its multiplier valuations are

```text
v₂(q_m)=m,                    v₃(q_m)=1−m.
```

For nonzero `u`, unequal-valuation addition therefore gives the exact laws

```text
v₂(T_m(u)) = v₂(u)+m          if v₂(u)+m<0,
v₂(T_m(u)) = 0                if v₂(u)+m>0,

v₃(T_m(u)) = v₃(u)+1−m       if v₃(u)+1−m<0,
v₃(T_m(u)) = 0                if v₃(u)+1−m>0.
```

Equality is the sole cancellation wall at either prime. Consequently, if the output is a unit
at both multiplier primes, then

```text
−v₂(u) ≤ m ≤ v₃(u)+1.                                  (1)
```

This is an explicit finite interval whenever it is nonempty. If both transported valuations are
negative, the wait cancels from their sum:

```text
v₂(T_m(u))+v₃(T_m(u)) = v₂(u)+v₃(u)+1.                  (2)
```

Thus a step with simultaneous `2`- and `3`-adic debt raises total debt by exactly one, regardless
of the wait. A negative transported valuation also recovers the wait from that place alone.

## Proof Boundary

Lean checks the multiplier valuations, both negative and positive branches, the necessary
interval (1), and the simultaneous-debt law (2) in
[`PeriodicShell.lean`](../MatrixMortality/PeriodicShell.lean). The audited declarations are:

```text
PeriodicShell.shellStep_hasValue_two_of_negative
PeriodicShell.shellStep_unit_two_of_positive
PeriodicShell.shellStep_hasValue_three_of_negative
PeriodicShell.shellStep_unit_three_of_positive
PeriodicShell.shellStep_two_three_sum_of_both_negative
PeriodicShell.wait_mem_two_three_unit_interval
```

The result is one-step and exact. It does not assert that every successful path stays a unit at
`2` and `3`, nor that the endpoint conditions force every intermediate state into the interval.
A path may move one valuation debt across its wall and later repair it. Cancellation at either
equality wall can also raise the corresponding valuation. These histories are precisely the
remaining obstruction to iterating (1) into a finite search.

## Consequence

The synchronized carry sought in `D2-M01` has a rigid local skeleton. In the simultaneous-unit
chamber, each next wait lies in a state-computable finite interval. In the simultaneous-negative
chamber, the wait-independent quantity (2) advances deterministically. Any infinite branching
must therefore pass through mixed-sign chambers or cancellation walls; it cannot remain hidden
inside either of these two regimes.

This cuts the next attack to a global chamber-transition question: prove that accepting histories
visit the finite interval often enough to obtain an effective search, or exhibit a computation
carried by alternating debt transfer across the two walls. The existing `5`-adic shell guard must
remain synchronized throughout.

## Judgment

| Claim | Class | Judgment |
| --- | --- | --- |
| exact `2`- and `3`-adic wall laws | theorem | Lean checked |
| simultaneous-unit output bounds the wait | theorem | Lean checked |
| simultaneous negative debt rises by one | theorem | Lean checked |
| the interval alone decides the benchmark shell | rejected | intermediate states may transfer or cancel debt |
| every successful path enters the simultaneous-unit chamber | open | requires a global chamber theorem |

