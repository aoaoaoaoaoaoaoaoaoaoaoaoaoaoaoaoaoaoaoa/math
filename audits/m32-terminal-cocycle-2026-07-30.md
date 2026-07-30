# M₃(2) terminal-defect cocycle audit

Date: 2026-07-30

## Coordinate contraction

For `C=A−L`, define the terminal defect

```text
T(m,n)=Cm+Dn.
```

The integral decoded step

```text
pˢᵃ m̃=(A−Lpᵃ)m+Dn,
ñ=T(m,n)
```

becomes

```text
pˢᵃ m̃=T+L(1−pᵃ)m,
pˢᵃ T(m̃,ñ)=(C+Dpˢᵃ)T+CL(1−pᵃ)m.
```

Both identities are direct polynomial consequences of `IntegralStep`.

## Reduced denominator recurrence

Suppose `(m̃,ñ)=g(m₁,n₁)` and

```text
T(m₁,n₁)=h n₂.
```

Eliminating `m` and `m₁` gives

```text
g pˢᵃ h n₂
  = g(A−Lpᵃ+Dpˢᵃ)n₁ − DL(1−pᵃ)n.
```

The theorem retains the signed common factors. No positivity, primality,
nonzeroness, or hidden division hypothesis is used.

## Fixed versus novel cancellation

For a primitive input and primitive reduced output, let `d` be coprime to
`pDL`. The determinant support theorem and the terminal-congruence theorem
combine to give

```text
d ∣ g
  ↔
d ∣ pᵃ−1
  and
(A−L)m ≡ −Dn (mod d).
```

Thus the outside-support component of `g` is exactly the intersection of a
cyclotomic divisor with the current terminal divisor.

## Adversarial example

For the checked period-three parameters

```text
p=3, s=2, A=−953, D=473, L=2240,
```

the primitive residual cycle is

```text
1/1 ─1→ 5/17 ─2→ 43/283 ─3→ 1/1.
```

The raw steps and reductions are

```text
(-800,-2720)   = -160(5,17),
(-1204,-7924)  = -28(43,283),
(-3440,-3440)  = -3440(1,1).
```

Each of `160`, `28`, and `3440` divides `DL=473·2240`. The denominator
height therefore grows `1,17,283` and collapses to `1` using fixed-support
cancellation alone.

This refutes any proposed monotonicity theorem for ordinary primitive height
or total common cancellation. It leaves open a height after quotienting the
finite `S`-unit directions belonging to primes dividing `DL`.

## Lean artifacts

- `ReturnGuard.integralStepNumerator_eq_terminalDefect_add`
- `ReturnGuard.integralStep_terminalDefect`
- `ReturnGuard.reducedDenominator_recurrence`
- `ReturnGuard.integralStep_novel_cancel_iff_cyclotomic_terminalCongruent`
- `ReturnGuard.Examples.cycle_integral_step_zero`
- `ReturnGuard.Examples.cycle_integral_step_one`
- `ReturnGuard.Examples.cycle_integral_step_two`
- `ReturnGuard.Examples.cycle_integral_reductions`
- `ReturnGuard.Examples.cycle_commonFactors_dvd_fixedSupport`
