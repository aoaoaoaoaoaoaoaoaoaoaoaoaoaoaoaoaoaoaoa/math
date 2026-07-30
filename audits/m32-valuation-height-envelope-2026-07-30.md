# M₃(2) valuation and height envelope audit

Date: 2026-07-30

## Cancellation size

For a primitive source pair, every common reduction factor `g` coprime to the base divides

```text
DL(pᵃ−1).
```

Consequently

```text
|g|≤|DL||pᵃ−1|
```

and, for every prime `ℓ`,

```text
vℓ(g)≤vℓ(D)+vℓ(L)+vℓ(pᵃ−1).
```

This corrects the first interpretation of the complete cancellation law. Its exact displacement
term contains `vℓ(m)`, but source primitivity and determinant support remove that term from the
attainable size bound.

## Lifting the exponent

For odd `ℓ`, a seed period `r` satisfying `ℓ∣pʳ−1`, and nonzero `k`,

```text
vℓ(p^(rk)−1)=vℓ(pʳ−1)+vℓ(k)
            ≤vℓ(pʳ−1)+logℓ(k).
```

At `ℓ=2`, the proof splits on the parity of `k`.

- Odd `k`: the valuation equals `v₂(pʳ−1)`.
- Even `k`: two-adic lifting gives

  ```text
  v₂(p^(rk)−1)+1
    =v₂(pʳ+1)+v₂(pʳ−1)+v₂(k).
  ```

Both yield a constant plus `log₂(k)`.

## Archimedean envelope

Let

```text
H(m,n)=max(|m|,|n|),
K=|A|+|D|+|L|.
```

The unscaled numerator satisfies

```text
|Nₐ(m,n)|≤(|A|+|D|+|L|pᵃ)H(m,n).
```

If the next numerator is nonzero, the integral step identity gives

```text
pˢᵃ≤|Nₐ(m,n)|.
```

For `p>1` and `s≥2`, canceling `pᵃ` yields

```text
p^((s−1)a)≤KH(m,n),
```

and hence

```text
a≤log_p(KH(m,n)).
```

The same estimates on both output coordinates give

```text
H(m̃,ñ)≤KH(m,n).
```

Factoring `(m̃,ñ)=g(m′,n′)` cannot increase height, so the reduced pair satisfies the same
bound.

## Strategic boundary

The recurrence cannot select a wait superlogarithmic in its current rational height, and one
transition cannot amplify height by more than a fixed factor. Therefore waits along an orbit
grow at most linearly in elapsed steps.

This does not decide reachability. A counter machine needs only linear counter growth, and
exponential projective height remains available. The unresolved mechanism is the sequence of
terminal congruences selecting rational inverse branches, not uncontrolled normalization size.

## Lean artifacts

- `ReturnGuard.integralStep_commonFactor_padicValInt_le_support`
- `ReturnGuard.integralStep_commonFactor_natAbs_le_support`
- `ReturnGuard.padicValNat_pow_mul_sub_one_le`
- `ReturnGuard.padicValNat_two_pow_mul_sub_one_le`
- `ReturnGuard.integralStep_wait_le_log_height`
- `ReturnGuard.integralStep_next_height_le`
- `ReturnGuard.integralStep_reduced_height_le`

All are in
[`ReturnGuardValuation.lean`](../MatrixMortality/ReturnGuardValuation.lean).
