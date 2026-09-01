# M₉(2) tilted geometric-tail rank-nine audit

Date: 2026-08-31  
Record: `MM-O27`  
Evidence: formalized

## Claim

At deletion width three and body `bb`, fix the benchmark paired roles `T,D_b,D_c` and column

```text
u=(67,0,81,−1)ᵀ.
```

For rational `q,λ,τ` with `q<−3/2`, define

```text
M₀=T,  M₁=D_b,  M₂=D_c,
Mₙ₊₃=λτⁿu(1,q,q,q).
```

Every exact rational transfer realization `Mₙ=VAⁿU` has at least nine states. The tail amplitude
and eigenratio are unrestricted; either may vanish.

## Exhaustion

Lean checks four sparse `9 × 9` block-Hankel minors with a common seven-row kernel elimination.
The remaining two coordinates are killed by the following exhaustive split:

1. `λ=0`: a zero-tail minor is nonsingular.
2. `λ≠0` and `209357λ−473489874≠0`: a generic-scale minor is nonsingular.
3. `λ=473489874/209357` and the primary affine pivot is nonzero: the primary minor is
   nonsingular.
4. At the exceptional scale with primary pivot zero, that equation determines `τ`. Substitution
   into the final pivot makes it strictly negative whenever `q<−3/2`, so the final minor is
   nonsingular.

Every selected block-Hankel matrix factors as a `9 × n` future factor times an `n × 9` past
factor through any proposed `n`-state realization. A nonzero determinant therefore gives `9≤n`.

## Boundary

The result proves that the `MM-C05` benchmark realization has exact transfer rank nine and closes
all parameter retunings of its uniform tilted row and single geometric tail inside the injective
same-zero chamber. It does not rule out moving or changing the three early roles, a tail with
several modes, nonlinear state, or a compiler which preserves only existential zero reachability.

`MatrixMortality/TiltedGeometricHankel.lean` checks the moment family, all four kernel
certificates, the exhaustive arithmetic split, transfer-Hankel factorization, and the cardinal
lower bound.
