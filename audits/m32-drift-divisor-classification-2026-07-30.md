# M₃(2) drift-divisor certificate classification

Date: 2026-07-30

## Setting

Write the integral guarded parameters as `(p,s,A,D,L)`. Let `ℓ` be a primitive prime divisor
of `pᵉ−1` and suppose `ℓ∣D`. Modulo `ℓ`, every residual transfer is

```text
⎡ A−Lpʳ             0 ⎤
⎣ pˢʳ(A−L)          0 ⎦,
```

where `r` is the wait modulo `e`.

Define

```text
O={Lpʳ : 0≤r<e}⊆𝔽ℓ.
```

## Exact classification

The quotient admits a closed invariant containing the reset while excluding annihilation and
the terminal ray if and only if `A∉O`.

The reverse direction is the known affine-shell construction. Orbit avoidance makes both first
column entries nonzero for every residue, so every nonzero affine ray maps to another nonzero
affine ray. The reset lies in this shell, while the terminal residual reduces to zero.

The forward direction removes a possible loophole. Suppose `A=Lpʳ`. Apply residue `r` directly
to the reset ray.

- If the first column is zero, closure forces the annihilation state.
- Otherwise its top entry is zero and its bottom entry is nonzero, so closure forces the
  terminal zero ray.

Thus no smaller invariant, exotic state selection, or delayed transition can rescue a failed
orbit test. This classifies every safe invariant at a drift divisor, not only the canonical
affine shell.

The zero residue belongs to the orbit. Avoidance therefore already implies `A−L≠0`; the old
terminal-denominator premise is redundant.

## Cyclic subgroup form

The residue class of `p` has multiplicative order exactly `e`. When `A` and `L` are nonzero,

```text
A∈O  ⇔  A/L∈⟨p⟩⊆𝔽ℓ×.
```

The proof extracts and reuses the exact-order theorem implicit in the primitive-divisor
development. It also proves `e∣ℓ−1`.

If `L` survives, multiplication by `L` preserves cardinality and the `e` powers are distinct.
Hence

```text
|O|=e,
```

and exactly `ℓ−e` center residues certify immortality. The yield is controlled by the index of
`⟨p⟩`:

- `e=ℓ−1`: only the zero center residue certifies;
- `e≪ℓ`: almost every center residue certifies.

This is a substantive stratum rather than an isolated congruence trick. The period-three
parameters have `(ℓ,e)=(11,5)`, so six of eleven center residues pass; their actual residue is
one of them.

## Executable criterion

`driftDivisorCertifies` computes membership in the finite orbit. Lean proves that it returns
true exactly when any safe quotient certificate exists. A true result feeds the canonical
decoded-integral lift and produces physical immortality.

This is a complete decision procedure for one drift-divisor quotient. For a fixed nonzero drift
numerator in the chosen integral presentation, the entire parameter-divisor branch is therefore
a finite search over its prime factors.

## Boundary

The theorem does not decide the guarded recurrence. A failed drift-divisor test only eliminates
that quotient. Primitive factors not dividing `D` have genuinely projective transfer matrices;
their automata may saturate or enter cancellation. The local-global campaign now begins there.

## Lean artifacts

- `IsPrimitivePrimeDivisor.unit_orderOf_eq_exponent`
- `IsPrimitivePrimeDivisor.exponent_dvd_prime_sub_one`
- `ReturnGuard.centerPowerOrbit`
- `ReturnGuard.affineSurvivors_quotientInvariant_iff_centerPowerOrbit_avoids`
- `ReturnGuard.HasQuotientCertificate`
- `ReturnGuard.hasQuotientCertificate_iff_centerPowerOrbit_avoids`
- `ReturnGuard.mem_centerPowerOrbit_iff_centerRatio_mem_zpowers`
- `ReturnGuard.card_centerPowerOrbit`
- `ReturnGuard.card_certifyingCenters`
- `ReturnGuard.driftDivisorCertifies`
- `ReturnGuard.hasQuotientCertificate_iff_driftDivisorCertifies`
- `ReturnGuard.not_physical_isMortal_of_driftDivisorCertifies`
- `ReturnGuard.Examples.cycle_driftDivisorCertifies`

The classification is in
[`ReturnGuardDriftCertificate.lean`](../MatrixMortality/ReturnGuardDriftCertificate.lean); the
concrete certificate is in
[`ReturnGuardQuotientExamples.lean`](../MatrixMortality/ReturnGuardQuotientExamples.lean).
