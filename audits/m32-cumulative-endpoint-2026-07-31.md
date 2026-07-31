# M₃(2) cumulative endpoint audit

Date: 2026-07-31

## Canonical state

For `α=A/L` and `ρ−α=D/L`, the cumulative endpoint pair starts at

```text
(R₀,β₀)=(A+D−L,1)
```

and one wait `a` satisfies

```text
p^(sa)β′=R−L(pᵃ−1)β,
R′=DR+(A−L)β′.
```

The target is unique. Every primitively reduced residual step induces this relation after its
removed signed content is absorbed into the target pair. Content is a derived local factor, not
part of the dynamical state.

Two consecutive steps give

```text
p^(sb)β″=(A+Dp^(sa)−Lpᵇ)β′+DL(pᵃ−1)β.
```

With `R₋₁=1`, the numerator recurrence is

```text
p^(sa)R′=(Dp^(sa)+A−Lpᵃ)R+DL(pᵃ−1)R₋₁.
```

Terminality is `R=0`. The full endpoint product transports the reset pair to
`p^(sΣaᵢ)(R,β)`, so its terminal truncant is the cumulative numerator after removal of the
forced base power.

## Repaired derivations

The reverse-resultant argument needs

```text
pᵃ−1 ∣ p^(sa)−1.
```

The report silently replaced the former by the latter. Lean now exposes the missing geometric
factor via `sub_one_dvd_pow_sub_one` before eliminating the wait.

The reported unit-tail recurrence also contained an erroneous factor `Xᵢ` in its numerator.
For `Xᵢ=Lβᵢ/βᵢ₊₁`, the checked identity is

```text
Xᵢ₊₁ = Lp^(saᵢ₊₁) /
  (D(p^aᵢ−1)Xᵢ + A + Dp^(saᵢ) − Lp^aᵢ₊₁).
```

## Exact examples

Lean checks the terminal executions

```text
(308,1) → (−12152,−4) → (0,−1240),
(−67704,1) → (7041216,−504) → (0,41664),
```

and the projective period-three execution

```text
(−2720,1) → (1267840,−800) → (−15411200,192640)
          → −15411200·(−2720,1).
```

The period-three example prevents monotonicity claims for cumulative or primitive height.

## Boundary

The old terminal-defect cocycle was a normalization-dependent projection of this recurrence and
has been deleted. The exact algebra does not prove that infinite rational executions are
eventually projectively periodic. The proposed closure is a blockwise height theorem: a wait
attaining a new maximum must expand projective height beyond the available p-adic division unless
the block already fixes a rational ray. That mountain-gap statement remains unproved.
