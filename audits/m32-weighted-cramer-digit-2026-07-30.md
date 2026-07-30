# M₃(2) Weighted Cramer-Digit Audit

Date: 2026-07-30

## Question

Does the periodic base expansion of a rational center/reset pair force the successive escape
digits in the parameter-lifting construction to be eventually periodic?

The answer in fixed coordinates is yes. The proposed inference to guard escape digits is false:
those digits are read in a moving Cramer frame whose transverse denominator can have arbitrary
p-adic depth.

## Scale-Free Solver

Write two consecutive center/reset sensitivities in mass/reset jet coordinates:

```text
g  = q  · (j₀−j₁,j₁),
g' = q' · (j₀'−j₁',j₁'),
λ  = q'/q,
κ  = q'(j∧j').
```

Lean verifies that the raw Cramer solver is exactly the weighted solver

```text
d_center =
  ((oldTarget−oldValue) λ j₁' + j₁ newValue) / κ,

d_reset =
  (−(j₀−j₁)newValue
   −(oldTarget−oldValue) λ(j₀'−j₁')) / κ.
```

The incoming integrating factor `q` cancels. For one legal guard step, `λ=−C` and `κ` is the
renormalized transverse defect already isolated by `R32-S24`.

This rectifies the name of the obstruction. Sensitivity magnitude is not the arithmetic cost
of lifting. Transverse defect is.

## Unbounded Denominator

For every positive `N`, the explicit unit tail

```text
X_N = (1+p^N−p^(sa))/(p^a−1)
```

has legal payload `1+p^N`. With old value and target zero, new value one, scale one, and reset
gradient `(0,1)`, Lean proves

```text
d_center = 1/p^N
```

and hence `v_p(d_center)=−N`.

Therefore no fixed denominator, integral weighted lattice, or bounded alphabet contains every
escape digit. The obstruction is uniform in the prime, positive depth, positive wait, and
positive prescribed transverse depth.

## What Rationality Does Give

Let `b` be coprime to a base `p`. Multiplication by `p⁻¹` permutes `ZMod b`. If `rₙ` denotes
the least nonnegative representative of the resulting orbit, define

```text
dₙ = (p rₙ₊₁−rₙ)/b.
```

Lean proves:

```text
0 ≤ dₙ < p,
−rₙ/b = dₙ + p(−rₙ₊₁/b),
dₙ₊φ(b) = dₙ.
```

It also connects the initial remainder to an arbitrary rational number up to an integer offset
and gives a common period `φ(b₀)φ(b₁)` for a rational pair. Thus the ordinary denominator-digit
stream is a genuine periodic base expansion, not merely a periodic modular proxy.

## Moving-Basis Obstruction

Suppose a parameter refinement is written in one frame as

```text
θ = d + Bξ
```

and the next frame is `BT`. Lean proves the exact tail law

```text
ξ = d + Tξ'.
```

The fixed-coordinate recurrence would have a scalar base in place of `T`. Here `T` changes with
the guard orbit. Periodicity of the rational coordinates therefore does not imply periodicity of
the Cramer digits unless the frame cocycle is independently controlled.

An exact base-three certificate displays all quantities in one stage:

```text
old jet       = (1,1),
new scale     = −2/9,
new jet       = (−7/2,−97/2),
κ             = 10,
weighted digit = (−7/9,−1).
```

The same file verifies that the ternary denominator digits of `−1/2` are constantly one. This
juxtaposition separates ordinary rational periodicity from moving-frame arithmetic concretely.

## Semantic Audit

- Every scale cancellation theorem states the required nonzero scale and transverse hypotheses.
- The arbitrary-depth witness is an exact rational identity, not an asymptotic valuation bound.
- The denominator-digit construction assumes the denominator is nonzero and coprime to the
  base.
- Euler period is an upper bound; no minimal-period claim is made.
- The moving-basis theorem is a general field identity. It does not assert that every abstract
  frame sequence occurs along a legal guard orbit.
- The result refutes only the fixed-coordinate periodicity argument. It neither proves nor
  disproves the existence of a finite nucleus for the full skew product.

## Strategic Consequence

The next state is not the digit alone. It is the digit together with the normalized Cramer
frame. The decisive object is therefore a rational matrix cocycle over a periodic denominator
stream.

A decision attack should derive the exact consecutive-frame transition, normalize it
projectively and p-adically, and search for an effective finite nucleus. A universality attack
should prove that the same transition transports unbounded `κ`-depth as a writable carry with
arbitrary finite prefix synthesis.

## Verification

The checked declarations live in:

- `MatrixMortality/RationalPadicDigits.lean`;
- `MatrixMortality/ReturnGuardParameterDigits.lean`;
- `MatrixMortality/ReturnGuardParameterDigitsExamples.lean`.

The full repository gate `./scripts/check.sh` is the acceptance test. Public declarations are
included in `AxiomAudit.lean`; their reviewed output is pinned in `verification/axioms.txt`.
