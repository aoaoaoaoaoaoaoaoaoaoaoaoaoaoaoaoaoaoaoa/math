# M₃(2) complete cancellation audit

Date: 2026-07-30

## Claim

Let one integral decoded step be

```text
pˢᵃ m̃ = (A−Lpᵃ)m+Dn,
ñ      = T(m,n)=(A−L)m+Dn,
```

and suppose

```text
(m̃,ñ)=g(m′,n′),    gcd(m′,n′)=1.
```

For every integer `d` coprime to `p`,

```text
d ∣ g
  ↔
d ∣ T(m,n)
  and
d ∣ L(1−pᵃ)m.
```

For every prime `ℓ≠p`, if `g`, `T(m,n)`, and `L(1−pᵃ)m` are nonzero, this is equivalent at all
prime powers to

```text
vℓ(g)=min(vℓ(T(m,n)), vℓ(L(1−pᵃ)m)).
```

## Proof decomposition

1. Primitivity of `(m′,n′)` gives

   ```text
   d ∣ g ↔ d ∣ m̃ and d ∣ ñ.
   ```

2. The denominator identity identifies `ñ` with `T(m,n)`.
3. The difference identity gives

   ```text
   pˢᵃm̃−ñ=L(1−pᵃ)m.
   ```

   Hence divisibility of both raw coordinates implies divisibility of the displacement.
4. Conversely, terminal and displacement divisibility imply `d ∣ pˢᵃm̃`. Coprimality of `d`
   with `p` cancels the power `pˢᵃ`.
5. Apply the divisor equivalence to every power `ℓᵏ`. The largest admissible exponent is the
   minimum of the terminal and displacement valuations.

No positivity hypothesis, canonical choice of `g`, or cyclotomic hypothesis is used.

## Consequences

The earlier fixed/novel split is strategic rather than algebraic. Every non-base cancellation
is terminal–displacement intersection.

- Outside the primes dividing `Lm`, cancellation can occur only through `pᵃ−1`.
- At fixed parameter primes, the source valuation `vℓ(m)` is part of the state and may be
  unbounded.
- Determinant support bounds the possible prime support but loses the exact multiplicities now
  exposed by the minimum formula.

This sharpens the finite-nucleus obligation. Removing a fixed set of prime labels is
insufficient; their valuation vector must be transported or bounded.

## Lean artifacts

- `ReturnGuard.integralStep_cancel_iff_terminalDefect_and_displacement`
- `ReturnGuard.integralStep_commonFactor_padicValInt`

Both are in
[`ReturnGuardArithmetic.lean`](../MatrixMortality/ReturnGuardArithmetic.lean).
