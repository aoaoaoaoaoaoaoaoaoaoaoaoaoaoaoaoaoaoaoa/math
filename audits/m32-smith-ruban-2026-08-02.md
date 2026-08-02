# `M₃(2)` Smith split and maximal-cancellation audit

Date: 2026-08-02

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Scope

This audit reconstructs the proposed depth-two endpoint split independently from the integral
recurrence already checked in Lean. It distinguishes the exact local theorem from the submitted
multi-wait cocycle and its claimed tropical path bound.

Let one primitive endpoint reduction remove signed forward content `h` and admit complementary
signed content `k`, so

```text
h k = DL(q−1),      q=pᵃ.
```

The audited claims are the signed factor split, the unimodular decoder, its Archimedean
contraction away from maximal cancellation, the maximal-cancellation recurrence, and the
allocation of an arbitrary divisor of `q−1` between `h` and `k`.

## Signed split

Write `g=gcd(h,DL)` in the integral gcd convention and remove its sign from the first residual
factor. There are integers `η,θ` and positive integers `u,v` satisfying

```text
h=ηu,    k=θv,    ηθ=DL,    uv=q−1,    gcd(u,θ)=1.
```

Lean proves existence directly from Bézout coprimality and cancellation. The split is used only
through these equations; no auxiliary quotient is promoted to dynamical state.

For any `core∣q−1`, the general gcd-quotient allocation lemma gives

```text
Ω = core/gcd(core,|h|)  divides |k|,
core ≤ |h|Ω.
```

The target denominator is coprime to `Ω`. This is stronger and cleaner than isolating a
special “primitive core”: it applies with multiplicity to every chosen divisor, while the
existing cyclotomic-complement theorem supplies the useful choices.

## Unimodular decoder

With source denominator `t`, target denominator `t′`, and scale `L`, define

```text
ρ = Lv t + q²ηt′,
σ = Lt   + (q+1)uηt′.
```

Equivalently,

```text
[ρ]   [v  q²      ][Lt ]
[σ] = [1  (q+1)u][ηt′].
```

Since `uv=q−1`, the decoder determinant is `−1`, and therefore

```text
ηt′ = ρ−vσ,
Lt  = q²σ−(q+1)uρ.
```

Every common divisor of `ρ,σ` consequently divides `Lη`; primitive normalization has no
unbounded hidden cancellation beyond the fixed coefficient support.

In the norm `||(x,y)||=|x|+4|y|`, if `q≥3`, `u≥1`, `v≥2`, and `uv=q−1`, then

```text
4 ||C(q,u,v)x|| ≤ 3q² ||x||.
```

Thus every `v≥2` branch contracts after the natural `q²` rescaling. The only branch not covered
by this uniform gap is maximal cancellation `v=1`, equivalently `u=q−1`.

## Maximal throat

For `v=1`, put

```text
m = Lt + q²ηt′.
```

The endpoint recurrence becomes exactly

```text
r=(q−1)m,
ηr′ = Dm + (A−L)ηt′.
```

If the next step is also maximal, substituting `r′=(q′−1)m′` yields the submitted
first-order chain law. This is the sole surviving noncontracting local throat; it is not yet a
global orbit classification.

## Frame correction

The submitted concatenating cocycle changed the target wait from `q` to `Q` inside one matrix
without changing coordinates. That identity is false in general. In the wait-adapted frame

```text
F_q(m,n) = (n, q²m−n),
```

the exact local identity is lagged:

```text
M_q F_q(m,n) = q²h F_q(m′,n′).
```

Changing the target frame is a separate gauge

```text
J(q,Q) = [[1,0],[Q²/q²−1,Q²/q²]],
J(q,Q)F_q(m′,n′)=F_Q(m′,n′).
```

Therefore the honest variable-wait cocycle is `J(q,Q)M_q`. Omitting `J` leaves an uncancelled
term depending on `(Q²−q²)m′`; it vanishes only in special cases. The report's ensuing
global tropical path estimate and superlacunary dichotomy are rejected: they depend on the
false ungauged identity and receive no registry record.

## Checked boundary

Lean checks:

- existence and all invariants of the signed Smith split;
- arbitrary divisor allocation and its denominator-coprimality consequence;
- decoder determinant, inverse, and common-divisor equivalence;
- the `3/4` weighted contraction for every `v≥2` branch;
- source and reset-defect factorization through the decoder;
- the maximal-cancellation recurrence and its two-step chaining law;
- the generic lagged cocycle, the rational frame gauge, and their exact composition.

Artifact: [`ReturnGuardSmith.lean`](../MatrixMortality/ReturnGuardSmith.lean).

## Strategic consequence

The Smith split does not prove global contraction. It yields a rigorous dichotomy:

1. `v≥2`: an explicit uniform Archimedean loss after natural rescaling;
2. `v=1`: all of `q−1` is swallowed forward, leaving the exact maximal recurrence.

The next attack must amortize the gauged products or classify repeated maximal steps. Any proof
which concatenates the lagged matrices without their frame gauges is invalid.
