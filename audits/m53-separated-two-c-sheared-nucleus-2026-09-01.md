# Sheared two-c finite-nucleus audit

Date: 2026-09-01

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Claim

For deletion width three, consider the sheared body

```text
q(t,n) = b^(3t+2) c b^(n+t) c b^n
```

and its coupled initial queue. Write `n+t=9k+3e+2` with `e<2`. Every source whose shear
phase differs from `e` halts. These are the four phase-mismatched families

```text
t+e=3u+1    or    t=3u+2.
```

The result does not decide the matched phase `t=3u+e`, the residue-eight continuations, or
two-`c` bodies outside the sheared plane.

## Normal Form

Put `m=3k+e`, so the middle run is `r=3m+2`, and define

```text
J = 4m+2t+5,    H = 7m+2t+9,
D₀ = 2J−1,      T₀ = 2J+1.
```

Every unresolved residual is one of two centered pair queues. Listing unary gaps gives

```text
D(z) = [D₀+z, r, J, r, n+1],
T(z) = [J−2, r, T₀+z, r, J, r, n+1].
```

Exact tag executions realize the partial map

```text
D(3z)   → D(z),      D(3z+H) → T(z),
T(3z)   → T(z),      T(3z−H) → D(z).
```

A missing branch is not an assumed terminal symbol: every `c` is proved absent from the
width-three deletion heads, and the resulting queue is drained by the tag semantics.

## Finite Nucleus

The live signed chamber is

```text
D(z): 0 < 3z < H,       T(z): −H < 3z < 0.
```

Every branch preserves this finite chamber. A successor has at most one predecessor in it.
For a sign-compatible distance `q`, the scalar form is

```text
F_H(q) = q/3       if q≡0 (mod 3),
         (H−q)/3   if q≡H (mod 3),
         terminal  otherwise.
```

The image omits the central interval `H/9<q<2H/9`. A state rooted in this gap is therefore
predecessor-free. Recursive deletion of the root from the finite chamber proves accessibility;
the argument does not assert that arbitrary centered states or arbitrary values of `H` halt.

The complementary residual is exactly `T(−d₁)` with

```text
d₁ = 4k+u+e+2,    H = 21k+6u+5e+11.
```

The shear-residue-two residual is exactly `D(d₂)` with

```text
d₂ = 3k+u+e+2,    H = 21k+6u+7e+13.
```

Lean proves `H<9dᵢ<2H` in both cases, placing both defects in the omitted image interval.

## Computational Audit

Computation preceded the proof and is not theorem evidence. An exact queue-level Python
simulator enumerated every feasible parameter with `1≤k<50`, then an abstract D/T simulator
extended the enumeration through `k=300`; neither found a cycle. A compiled scalar-map sweep
checked every feasible `u≤3k` for `k≤20000`, followed by ten million deterministic
pseudorandom cases with `k<10⁹`; no countercycle appeared, and the longest tortoise trace had
29 turns. A separate search found cycles for generic `H`, ruling out the stronger inference
that contraction alone proves termination. The formal result uses only the exact image-gap
placement above.

## Formal Verification

[`MatrixMortality/SeparatedTwoCShear.lean`](../MatrixMortality/SeparatedTwoCShear.lean) checks
the two mixed-stroke histories and transfers mortality of each residual back to the coupled
source. [`MatrixMortality/SeparatedTwoCShearNucleus.lean`](../MatrixMortality/SeparatedTwoCShearNucleus.lean)
checks:

- the centered `D/T` relation, finite chamber, predecessor uniqueness, and image-gap roots;
- all four concrete tag-system successor macros and both terminal cases;
- the exact centered form and image-gap placement of both residual defects;
- mortality of all four phase-mismatched families through
  `SeparatedTwoCShear.shearedPhaseMismatch_tagHaltsFrom`.

The publication-facing declarations are listed in `AxiomAudit.lean`. The focused compiler,
environment-linter, forbidden-aperture, and reviewed-axiom-snapshot gates cover this result.
