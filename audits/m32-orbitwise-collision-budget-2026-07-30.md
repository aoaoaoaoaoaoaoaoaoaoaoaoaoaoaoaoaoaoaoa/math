# M₃(2) orbitwise collision-budget audit

**Date:** 2026-07-30  
**Status:** Lean-checked negative experiment; `M₃(2)` remains open

## Question

After localization away from the fixed support `D·L·p`, can the product of novel primitive
reduction factors along the canonical reset orbit be bounded by its endpoint tangent data?

## Exact product law

For a projective transfer chain

```text
Mᵢvᵢ=cᵢvᵢ₊₁,
```

Lean defines the chronological product and proves

```text
Mₖ₋₁⋯M₀v₀=(∏ᵢcᵢ)vₖ.
```

If the terminal ray `vₖ` is primitive, the product of the removed scalars is exactly the
content of the composed image:

```text
gcd((Mₖ₋₁⋯M₀v₀)₀,(Mₖ₋₁⋯M₀v₀)₁)=|∏ᵢcᵢ|.
```

This is an identity, not a descent. The composed transfer can acquire precisely the height
needed to pay for the accumulated content.

## Prescribed reset collision

The first canonical residual pair is `(1,1)`. Fix a wait `a`, a depth `s`, a center numerator
`A`, and a factorization

```text
pᵃ−1=q r.
```

Set

```text
D=pᵃ+q p^(sa)−A.
```

Then the exact integral guard step is

```text
(1,1)  ⟶  q·(1,p^(sa)+r).
```

The target pair is primitive, so `q` is the complete common reduction factor. At center two,
`q` is coprime to the fixed support `D·p`: modulo `q`,

```text
D≡−1.
```

Hence a ready reset can swallow any prescribed divisor of `pᵃ−1` on its first legal step
without reclassifying that divisor as fixed support. There is no parameter-uniform novel-factor
bound depending only on dimension, base, depth, or endpoint primitivity.

## One canonical four-collision ladder

The stronger counterexample fixes one guard:

```text
(p,s,α,ρ)=(3,2,−64,52569),       D=52633.
```

Its canonical residual orbit begins

```text
1
  --4--> 1/6571
  --2--> 2134885/172925689
  --2--> 384806441/31169380211
  --1--> 91139567034112/820256488113449.
```

Every arrow is a legal decoded step. The primitive integral lifts remove common factors

```text
8, 2, 292, 2.
```

The factor `292=73·4` has fixed component `73∣52633`; after fixed-support removal, the four
successive novel factors are

```text
8, 2, 4, 2.
```

Thus novel cancellation on the reset orbit is neither hypothetical nor confined to one
exceptional collision. A finite quotient can fail, resume after normalization, and fail again
on the same deterministic execution.

## Adjudication

The product-content identity is accepted. The hoped-for endpoint-only budget is rejected in
every parameter-uniform form: reset and transfer height can absorb prescribed cyclotomic
content, and one fixed orbit already exhibits four successive novel collisions.

This does not establish an unbounded collision stack for one fixed parameter set. A
per-instance effective bound may still exist. Its proof cannot count collisions, assume that
only the first collision is novel, or compare accumulated content only with endpoint tangent
height.

The constructive alternative is now concrete. Readiness imposes `p`-adic congruences; swallowing
a new factor imposes a prime-to-`p` moving-kernel congruence. The next experiment should decide
whether these conditions can be composed by Chinese remaindering and lifting to synthesize
arbitrarily long canonical collision prefixes.

## Lean boundary

The following declarations are checked without project axioms:

- `ReturnGuard.ScaledTrajectory.chronologicalProduct_mulVec`;
- `ReturnGuard.ScaledTrajectory.image_gcd`;
- `ReturnGuard.prescribedReset_integralStep`;
- `ReturnGuard.prescribedReset_primitiveIntegralStep`;
- `ReturnGuard.prescribedReset_factor_isCoprime_fixedSupport`;
- `ReturnGuard.Examples.nestedNovel_decodedStep_zero`;
- `ReturnGuard.Examples.nestedNovel_decodedStep_one`;
- `ReturnGuard.Examples.nestedNovel_scaledTrajectory`;
- `ReturnGuard.Examples.cyclotomicLadder_decodedSteps`;
- `ReturnGuard.Examples.cyclotomicLadder_primitiveSteps`;
- `ReturnGuard.Examples.cyclotomicLadder_novelFactors`.

The generic laws are in
[`ReturnGuardTangentBudget.lean`](../MatrixMortality/ReturnGuardTangentBudget.lean); the exact
canonical trajectories are in
[`ReturnGuardTangentExamples.lean`](../MatrixMortality/ReturnGuardTangentExamples.lean).
