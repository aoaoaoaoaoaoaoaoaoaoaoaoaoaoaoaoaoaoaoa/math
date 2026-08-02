# M₃(2) Bounded-Denominator Periodicity Audit

Date: 2026-08-02

Author: GPT-5.6 Sol, elicited by @eternalism_4eva.

## Claim

Let `(rᵢ,tᵢ)` be an infinite stream of primitive endpoint pairs with positive denominators,
waits `aᵢ>0`, signed forward contents `hᵢ`, and complementary contents `kᵢ`, satisfying

```text
p^(s aᵢ) hᵢ tᵢ₊₁ = rᵢ − L(p^aᵢ−1)tᵢ,
hᵢkᵢ = DL(p^aᵢ−1),
```

for a prime `p`, depth `s≥2`, and p-adic units `D`, `L`, and `A−L`. If all `tᵢ` are positive
and bounded by a supplied `B`, then:

1. every nondecreasing pair `aᵢ≤aᵢ₊₁` lies below an explicit computable ceiling;
2. every wait lies below the maximum of that ceiling and `a₀`;
3. every primitive pair lies in an explicit finite integral rectangle;
4. some state repeats;
5. if state succession is functional, the stream is eventually periodic.

The Lean theorem is uniform in every depth `s≥2`; the earlier paper reconstruction only needed
the campaign's principal case `s=2`.

## Arithmetic Cut

Two consecutive reductions give

```text
p^(s aᵢ₊₁) hᵢ₊₁ tᵢ₊₂
  = (A + Dp^(s aᵢ) − Lp^aᵢ₊₁)tᵢ₊₁ + kᵢtᵢ.
```

For `aᵢ₊₁=aᵢ+η`, division by `p^aᵢ` exposes the integral error

```text
E = Lp^ηtᵢ₊₁
  + p^((s−1)aᵢ)(p^(sη)hᵢ₊₁tᵢ₊₂ − Dtᵢ₊₁).
```

Its absolute value is at most

```text
B(|A|+|DL|).
```

If `η<(s−1)aᵢ`, the first summand has the unique smaller p-adic order. Hence `p^η∣E`. Unless
the bracket vanishes, the Archimedean bound also controls `p^((s−1)aᵢ)`. If it vanishes,
p-unit comparison forces `η=0`; primitivity forces `tᵢ₊₁=1`; and

```text
Lp^aᵢ−A = kᵢtᵢ ∣ Dtᵢ(A−L),
```

which bounds `aᵢ`.

If `η≥(s−1)aᵢ`, then `p^((s−1)aᵢ)∣E`. A nonzero error bounds `aᵢ` immediately. A zero error
forces `η=(s−1)aᵢ` and

```text
(D−L)tᵢ₊₁ = p^(sη)hᵢ₊₁tᵢ₊₂,
```

again bounding `aᵢ`. Once the earlier wait is bounded, the primitive numerator equation boxes
the intermediate state, and its outgoing wait is logarithmic in that box. This is the missing
step between “the earlier wait is bounded” and “both waits are bounded.”

## Kernel Boundary

Lean checks the local arithmetic chain in `ReturnGuardPeriodicity.lean` and the finite-stream
consequence in `ReturnGuardFiniteOrbit.lean`, principally:

```text
PrimitiveEndpointReduction.denominator_recurrence
PrimitiveEndpointReduction.denominator_growth_factorization
PrimitiveEndpointReduction.nonDecreasing_wait_le_log_recordBound
PrimitiveEndpointReduction.wait_le_log_sourceBox
PrimitiveEndpointReduction.nonDecreasing_waits_le
BoundedPrimitiveEndpointStream.wait_le
BoundedPrimitiveEndpointStream.state_mem_box
BoundedPrimitiveEndpointStream.exists_state_repeat
BoundedPrimitiveEndpointStream.eventually_periodic
```

The theorem assumes a supplied denominator bound. It neither computes such a bound for an
arbitrary orbit nor decides the unbounded-denominator residue. It proves that every genuinely
nonperiodic survivor in this split-spectrum guard must use unbounded reduced denominators.

## Strategic Effect

Bounded-denominator universality is closed. The live constructive channel must grow an
Archimedean denominator register while preserving all p-adic readiness and endpoint-content
constraints. The decision-side target is correspondingly sharper: prove that unbounded
denominator growth eventually triggers a coefficient obstruction, a finite quotient reset, or
a height-forced repeated factor.
