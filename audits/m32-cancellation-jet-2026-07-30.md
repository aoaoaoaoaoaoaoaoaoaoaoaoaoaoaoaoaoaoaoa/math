# M₃(2) primitive-cancellation blow-up

Date: 2026-07-30

## Question

When an exact-order prime quotient reaches its absorbing cancellation state, can a bounded
amount of additional prime-local memory divide out the swallowed factor and resume the
projective orbit?

The answer is negative for every *uniform fixed congruence depth*. Primitive cancellation is a
projective blow-up. Its exceptional divisor retains an unrestricted tangent direction, and one
fixed integral recurrence realizes arbitrarily deep collisions on primitive inputs.

## Strict transform

Write the terminal term and cyclotomic displacement as

```text
T = ℓᵗT₀,
P N − T = ℓᵉC₀,
```

with `T₀,C₀` prime-local units. If `r=min(t,e)` and

```text
N=ℓʳN′,      T=ℓʳT′,
```

then Lean proves

```text
T′ = ℓ^(t−r)T₀,
P N′ = ℓ^(t−r)T₀ + ℓ^(e−r)C₀.
```

At a cyclotomic factor, `P≡1 mod ℓ`. Reduction therefore has exactly three forms:

```text
t<e:  [N′:T′]=[1:1],
e<t:  [N′:T′]=[1:0],
t=e:  [N′:T′]=[T₀+C₀:T₀].
```

Only the equal-depth chart transports information.

## Exceptional divisor

The equal-depth tangent is not confined to a proper projective subset. Over an arbitrary field,
choose `T₀=1` and `C₀=x−1`; this produces every affine point `x≠1`. The unequal-depth charts
produce one and infinity. Lean consequently proves that the cancellation exceptional divisor
surjects onto `ℙ¹`.

This identifies the precise loss in the ordinary quotient automaton. Its absorbing state
collapses an entire projective line of first nonzero jets, not one recoverable residue.

## Fixed truncation is insufficient

For every `N`, the two raw pairs

```text
(ℓᴺ, −ℓᴺ),       (ℓᴺ, ℓᴺ⁺¹)
```

coincide modulo `ℓᴺ`: both appear as `(0,0)`. After removing their maximal common powers, their
projective exits are zero and one. Thus no state determined by reduction modulo a fixed
`ℓᴺ` can resume every collision correctly.

This is stronger than saying that cancellation depth is numerically unbounded. It shows that
the first distinguishing digit can occur immediately beyond any proposed truncation and can
change the normalized projective state.

## Realizability inside the guard recurrence

The local blow-up is attained by actual primitive integral steps. Suppose

```text
pᵃ−1 = ℓᵈu,       ℓ∤u.
```

For arbitrary center numerator `A`, set

```text
R = u + ℓp^(2a),
T = ℓᵈR,
n = T − (A−1).
```

The primitive source `(1,n)` has the exact step

```text
(1,n) ↦ (ℓᵈℓ, ℓᵈR).
```

The reduced pair `(ℓ,R)` is primitive and represents zero modulo `ℓ`; the displacement has
exact leading unit `−u`. This construction is formalized uniformly in `p,ℓ,a,d,A`.

For the fixed parameters

```text
(p,s,A,D,L)=(5,2,29,1,1),
```

take

```text
a=2·3^(d−1).
```

Odd-prime lifting of the exponent gives

```text
v₃(5ᵃ−1)=d
```

for every `d>0`. Hence this single recurrence has primitive inputs realizing every positive
`3`-adic cancellation depth.

## Adjudication

The hypothesis that primitive cancellation admits a **uniform bounded finite-jet nucleus** is
rejected.

What remains possible is narrower and more interesting:

- an orbit-specific theorem may bound collision depth along the canonical reset orbit;
- a symbolic algorithm may carry exact valuations without factoring through a fixed finite
  quotient;
- an undecidability construction may use equal-depth tangent digits as an unbounded stack.

The current witness family varies the primitive source with `d`. It does not prove that one
fixed reset orbit realizes unbounded depth. That is now the exact frontier question.

## Lean artifacts

- `ReturnGuard.cancellationJet_eq`
- `ReturnGuard.cancellationJet_terminalDepth_lt_ofPair`
- `ReturnGuard.cancellationJet_displacementDepth_lt_ofPair`
- `ReturnGuard.cancellationJet_depth_eq_mod`
- `ReturnGuard.localCancellationExit_surjective`
- `ReturnGuard.cancellationExit_surjective`
- `ReturnGuard.cancellationExit_escapes_fixed_truncation`
- `ReturnGuard.padicValNat_five_pow_twice_three_pow_sub_one`
- `ReturnGuard.primitive_integralStep_of_exact_cyclotomicDepth`
- `ReturnGuard.exists_primitive_integralStep_with_three_cancellationDepth`
- `ReturnGuard.integralStep_cancellationExit`

The implementation is
[`ReturnGuardCancellationJet.lean`](../MatrixMortality/ReturnGuardCancellationJet.lean).
