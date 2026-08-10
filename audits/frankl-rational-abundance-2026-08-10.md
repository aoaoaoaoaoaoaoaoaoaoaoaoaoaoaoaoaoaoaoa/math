# Frankl conjecture: formal rational abundance theorem

Date: 2026-08-10

Author: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Verdict

For every finite nontrivial union-closed family `F`, some element belongs to strictly more than

```text
(76469/200000)|F| = 0.382345|F|
```

members. Lean checks the complete implication from a finite union-closed family through the
affine coupling inequality. The publication declaration is
`Frankl.unionClosed_exists_abundant_coordinate`.

Lean also proves the exact strict comparison

```text
(3−√5)/2 < 76469/200000.
```

The result is therefore an explicit rigorous improvement over the Alweiss–Huang–Sellke
constant. It is numerically smaller than Cambie's reported `0.382345533366703…` candidate and
Liu's conditional `0.382709087…` candidate. Those values have weaker evidence but remain the
correct numerical comparisons.

## Theorem scope

The formal statement represents a family as a `Finset (BitCube n)`, assumes closure under
coordinatewise union, nonemptiness, and inequality with the singleton family containing only
the zero vector. It returns a coordinate whose real-valued frequency is strictly greater than
`(76469/200000)|F|`. Every finite set family has such a Boolean-cube presentation after its
finite ground set is enumerated.

The theorem does not prove Frankl's conjectured half-frequency bound. It has not passed external
peer review. The priority claim is limited to the inspected literature recorded in
[`frankl-ad-fontes-review-2026-08-08.md`](frankl-ad-fontes-review-2026-08-08.md).

## Old and new boundary

| Seam | Prior state | Present state |
| --- | --- | --- |
| Explicit rigorous universal constant | `(3−√5)/2` in AHS | `76469/200000` |
| Local rational certificate | `19099/50000` | `76469/200000` |
| Union-closed entropy implication | informal finite bridge | Lean theorem |
| High endpoint rectangle | residual static subdivision plus a conditional-mean core | support-aware analytic contraction on `1/4≤a≤t`, `0≤q≤1/2` |
| Deterministic endpoint `q=1` | analytic corner plus static edge trace | dominated analytically by `q=a` |
| Remaining static certificate | low rectangle, high residual, and `q=1` edge | low rectangle only |

The comparison with Cambie is epistemic rather than numerical: `0.382345` is below
`0.382345533366703…`, but the former now has a complete checked proof and the latter remains a
reported numerical global minimum.

## Finite entropy bridge

Let `X` be uniform on the family. At each Boolean coordinate, its conditional success
probabilities form a finite marginal law whose mean is the coordinate frequency. Two global
self-couplings are constructed recursively:

1. the independent product coupling;
2. a symmetric dependent coupling using the local maximum-entropy Boolean kernel.

The checked finite orbit theorem applies to each conditional law. Shannon's chain rule and the
fact that conditioning cannot increase entropy sum the local inequalities into

```text
(1−α)H(X⁰∨Y⁰)+αH(X¹∨Y¹) ≥ (1+ε)H(X),
α=7/200, ε=10⁻⁷.
```

Union closure keeps both output laws inside the original family, so each output entropy is at
most `log |F|=H(X)`. If `|F|≥2`, the strict factor `1+ε` gives a contradiction. Singleton
families are discharged directly. Null conditioning fibers use the zero conditional-probability
convention and are proved harmless.

The bridge is implemented in `Frankl/FiniteEntropy.lean`,
`Frankl/ConditionalEntropy.lean`, `Frankl/FiniteCoupling.lean`, and
`Frankl/AffineEntropyBridge.lean`.

## Endpoint closure

The repaired fixed-mean reduction and half-support kernel leave diagonal laws and one
diagonal–endpoint family. The diagonal family is analytic. For the endpoint family, conditioning
away the deterministic coordinate produces center

```text
r=(a(1−2t)+tq)/(1+q−a−t).
```

On `1/4≤a≤t` and `0≤q≤1/2`, the actual support ceiling `max(a,q)` sharpens the join-curvature
loss. Monotonicity in `r` reduces the required coefficient bound to one quadratic sign when
`q≤a` and one cubic sign when `a≤q`. The saturated centered objective is positive by convexity
of its complement-coordinate curve on `1−t≤y≤21/25`; all logarithm estimates are rational
kernel proofs.

When `q=1`, replacing the deterministic endpoint atom by the symmetric orbit at `q=a`
preserves the marginal distribution and independent entropy. It decreases only the dependent
entropy term, proving

```text
J(a,a) ≤ J(a,1).
```

The low or high rectangle therefore already covers the whole `q=1` edge. Static replay remains
only on `0≤a≤1/4`, `0≤q≤1/2`. Regenerating the trace from
`tools/GenerateFranklEndpointTrace.lean` reproduces the committed sources byte-for-byte.

## Independent oracle

The Lean proof does not call Python or Arb. As an independent check,
`tools/certify_frankl.py` uses 160-bit Arb interval arithmetic and reports:

```text
diagonal-endpoint:       34868 assessed boxes; 17453 certified leaves
diagonal-diagonal-lower:  4036 assessed boxes;  2026 certified leaves
diagonal-diagonal-upper:  2176 assessed boxes;  1094 certified leaves
Frankl entropy certificate at 76469/200000: PASS
```

The deterministic hashes are recorded in [`SALVAGE.md`](../SALVAGE.md#fc-m01-rational-yu-certificate).
The same program with `--target 19099/50000` reproduces the earlier audit exactly.

## Formal trust boundary

`lake build Frankl` and the complete environment lint pass with warnings treated as errors and
automatic implicit variables disabled. The publication theorem and its four principal
intermediate declarations depend exactly on

```text
propext, Classical.choice, Quot.sound.
```

The repository scan finds no `sorry`, `admit`, project axiom, `unsafe`, `partial`,
`native_decide`, `implemented_by`, `run_tac`, external declaration, linter suppression, or
strictness relaxation. The reviewed output is frozen in `verification/axioms.txt`.
The repository-wide `scripts/check.sh` transaction also passes, including both compartmentalized
Lean libraries, Python lint and type checks, independent finite audits, reference hashes,
semantic HTML validation, and reproducible PDF generation.

## Other closed seams

The earlier campaign also closed two literature questions not used to strengthen this uniform
constant: Frankl's conjecture for bidual and self-dual Horn functions, and Zargar's omitted
binary `k=2,m=1` semigroup kernel, which yields a strict weighted theorem. Their statements,
scope guards, and evidence are in `FC-S01` and `FC-S03` of [`SALVAGE.md`](../SALVAGE.md) and in
the dedicated 2026-08-08 audits. They must not be conflated with the present universal uniform
bound.
