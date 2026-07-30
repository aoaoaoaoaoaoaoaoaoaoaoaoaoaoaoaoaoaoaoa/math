# M₃(2) Renormalized Parameter-Jet Audit

Date: 2026-07-30

## Question

The center/reset sensitivity grows by a singular multiplier of value `−sa`, while its
projective direction freezes. Does an integrating factor produce an iteration-ready finite
jet, or is the transverse precision itself unbounded?

## Exact Normal Form

Write the sensitivity in mass/reset coordinates:

```text
u = g₀+g₁,
r = g₁,
u' = 1−Cu,
r' = H−Cr.
```

Transport an auxiliary nonzero scale by `q' = −Cq` and put

```text
j(q,g) = (u/q,r/q).
```

Direct division gives

```text
j(q',g') = j(q,g) + (1,H)/q'.
```

Lean checks the identity without asymptotic notation. If `q` has value `v`, then `q'` has
value `v−sa`; both displayed increments have exact value `sa−v`. The renormalized jet
therefore moves by successively smaller p-adic corrections.

## Transverse Coordinate

Define

```text
κ(H,q,g) = (Hu−r)/q.
```

The numerator is the exterior product of `g` with its successor. Substitution gives

```text
κ(H,q',g') = κ(H,q,g).
```

For a different next payload `H'`,

```text
κ(H',q',g') = κ(H,q,g) + (H'−H)j(q',g')₀.
```

Thus singular transport does not create higher transverse data. Payload variation is its sole
forcing term. The rational state `(q,j,κ)` is fixed-dimensional.

## Arbitrary-Depth Obstruction

For positive `N`, define

```text
X_N = (1+p^N−p^(sa))/(p^a−1).
```

Both numerator and denominator are prime-free, so `X_N` is a p-adic unit. Its legal payload is
exactly `H=1+p^N`. At the reset gradient `(0,1)` and scale one,

```text
κ = H−1 = p^N.
```

Lean proves exact value `N`, for every prime and positive `s,a,N`. The conservation theorem
then preserves that value through every iterate of the corresponding constant stage.

This refutes the strongest hoped-for outcome: no renormalization places all transverse
directions in one fixed unit annulus, and no bounded precision budget suffices uniformly.

## Semantic Audit

- The gradient recurrence is the already checked center/reset derivative recurrence.
- Division requires explicit nonzero scale and multiplier hypotheses.
- Every valuation statement retains its nonzero side condition.
- The arbitrary-depth tail is a genuine rational p-adic unit.
- Constant-stage iteration is an algebraic cocycle experiment. It does not assert that one
  guarded state orbit repeats the same tail or payload.
- The result neither proves a rational infinite compatible lift nor proves that every such
  inverse limit is irrational.

## Strategic Consequence

The raw-gradient explosion was coordinate noise. The remaining obstruction is one scalar
depth in a fixed-dimensional recurrence:

```text
κ' = κ + (H'−H)j₀'.
```

The next attack should derive the weighted Cramer digit from this recurrence. A decision route
would prove that rational guard parameters force bounded or eventually periodic defect depth.
An undecidability route would construct one canonical rational orbit with unbounded prescribed
depth.

## Verification

The full repository gate `./scripts/check.sh` is the acceptance test. Public declarations are
included in `AxiomAudit.lean`; their reviewed output is pinned in `verification/axioms.txt`.
