# M₃(2) Universal-Boundary Audit

Date: 2026-08-05

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Enemy

`M₃(2)` asks whether mortality is decidable for every pair of `3 × 3` integer matrices. The
rank-`(3,2)` guard has already reduced one concrete family to deterministic rational
reachability. Its live residue consists of even-reset-defect executions with unbounded reduced
denominators which may repay every mandatory nonmaximal Smith loss.

This audit reconstructs a submitted prime-adic attack. Only claims which cut that residue are
retained; the submitted conversation and report remain transient.

## Adjudication

| Submitted claim | Class | Judgment |
| --- | --- | --- |
| the depth-two endpoint map has the displayed reset-defect factorization | promotion | checked directly from the existing endpoint transfer |
| two coefficient inequalities make the open reset ball invariant | promotion | checked for every positive decoded branch and every auxiliary prime |
| mortality forces the stated higher prime-power thresholds in the reset-defect numerator | consequence | follows arithmetically from the checked inequality theorem; the piecewise threshold is not duplicated in Lean |
| every prime dividing `p−1` must divide the reset-defect numerator | promotion | checked as a direct physical-mortality corollary |
| the supplied period-three ray is harmless | checked consequence | its coefficient valuations satisfy the stronger reset-ball hypotheses |
| an arbitrary common-period tail is trapped | rejected as stated | the tail entry must first lie in the corresponding reset ball |
| order-breaking bridges are the sole remaining global obstruction | qualified | they form a sharper cyclotomic lane, but do not replace the unconditional global amortization problem |

## Endpoint Factorization

Choose an integral coefficient presentation

```text
center=A/L,    drift=D/L,    R=A+D−L,
```

and set `q=pᵃ` at depth two. In the terminal endpoint coordinate `z`, the branch is

```text
F_q(z) = ((A−L+Dq²)z − (A−L)L(q−1)) / (z−L(q−1)).
```

Lean derives from the existing endpoint-transfer theorem the cross-multiplied identity

```text
(F_q(z)−R)(z−L(q−1)) = D(q−1)((q+1)z+L).
```

The proof does not introduce another execution, normalization, or dynamical coordinate.

## Reset-Ball Wall

Let `ℓ` be any prime and write

```text
λL=vℓ(L),   λR=vℓ(R),   λD=vℓ(D),
e=vℓ(p−1), ε=vℓ(2).
```

Assume `R≠0` and

```text
λR < λL+e,                                    (U1)
2λR < λD+e+min(λL,λR+ε).                      (U2)
```

Then every positive decoded branch preserves

```text
Bℓ(R,λR) = {R} ∪ {z : z−R≠0 and λR<vℓ(z−R)}.
```

Indeed, a point in this ball has valuation `λR`. Since `p−1∣q−1`, (U1) makes the two
denominator terms have unequal valuations and gives

```text
vℓ(z−L(q−1))=λR.
```

The numerator blade satisfies

```text
vℓ((q+1)z+L) ≥ min(λL,λR+ε).
```

Together with the factorization, (U2) puts the target strictly back inside the ball. Reset is
inside; terminal `0` is outside because `vℓ(−R)=λR`. The checked arbitrary-word compiler then
turns this branch invariant into physical immortality.

The submitted proof silently applied a finite-valuation calculation when
`(q+1)z+L=0`. In that branch the cross-multiplied identity and the already nonzero denominator
give `F_q(z)=R` exactly. The formal proof isolates this case before taking valuations.

Artifact: `ReturnGuard.not_physical_isMortal_of_resetBall` in
[`ReturnGuardBoundary.lean`](../MatrixMortality/ReturnGuardBoundary.lean).

## Coefficient Sieve

For every prime `ℓ∣p−1`, mortality forces

```text
ℓ ∣ R.
```

Otherwise `λR=0`, while `e≥1` and every integral coefficient valuation is nonnegative; both
(U1) and (U2) hold. Thus, in any integral presentation,

```text
rad(p−1) ∣ R
```

is a necessary condition for mortality. The full inequality theorem is stronger: it also
excludes coefficient tuples where `ℓ` already divides `R` but its valuation remains below the
reset-ball wall. Scaling `A,D,L` together translates `λL,λR,λD` equally, so both inequalities are
presentation-invariant.

Artifact: `ReturnGuard.universalBoundary_dvd_resetDefectNumerator_of_physical_isMortal` in
[`ReturnGuardBoundary.lean`](../MatrixMortality/ReturnGuardBoundary.lean).

For the fixed ray

```text
p=3,    A=−446,    D=500,    L=56,    R=−2,
```

the `2`-adic tuple is `(λL,λR,λD,e,ε)=(3,1,2,1,1)`, so (U1) and (U2) hold. The entire physical
law is immortal, not merely periodic on its displayed ray. No example declaration was retained:
the general theorem owns the result.

## Validation

The new module compiles under the repository's strict Lean gate, and both public declarations
have the reviewed transitive axiom set

```text
[propext, Classical.choice, Quot.sound].
```

Independent exact-rational checks covered 281,520 branch instances satisfying (U1) and (U2),
including the zero-blade branch. Exhaustive evaluation of 640 small valuation tuples agreed with
the submitted closed formula for the least failing threshold. Both previously checked mortal
guards lie on the permitted side of the coefficient sieve. These computations are audit
evidence only; the unbounded theorem rests on Lean.

## Common-Period Qualification

If an entire word starts at reset and every wait is divisible by `m`, the same proof may replace
`p−1` by `pᵐ−1`. More generally, a common-period tail is trapped only after its entry endpoint
has been proved to lie in the corresponding reset ball. Divisibility of its subsequent waits
does not supply that entry condition.

This separates the next cyclotomic obligation into two real cuts: use exact-order reset
incidence with sufficient multiplicity to enter a reset ball, then amortize the first bridge
whose wait breaks the common order. Neither cut is yet proved.

## Wound

```text
MASTER VERDICT: still open
REMOVED: every depth-two coefficient presentation satisfying (U1) and (U2), including every presentation with a prime divisor of p−1 absent from R; the supplied fixed ray is globally immortal
REMAINS: even-R, universal-boundary-divisible, unbounded-denominator executions capable of repaying all mandatory nonmaximal losses
DISTANCE: globally amortize the v≥2 losses or construct a survivor; in the cyclotomic lane, first prove reset-ball entry and then bound the first order-breaking bridge
```
