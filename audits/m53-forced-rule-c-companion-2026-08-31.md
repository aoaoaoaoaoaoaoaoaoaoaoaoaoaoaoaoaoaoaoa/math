# Forced-Rule Companion Toggle Wall

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the exact forced-rule companion makes the physical toggle invertible, contradicting
a rank-two delimiter cube

Nothing below proves `M₅(3)` decidable or undecidable. It closes the last exact
bordered-companion leaf left by `MM-O16`.

## Semantic Derivative

Every Neary terminal match begins with the rule-`c` role. Let

```text
h(w) = coefficient(R_c :: decode(w)).
```

The paired pushout represents this semantic left derivative by replacing its initial row with

```text
(1,x,2,x),
```

where `x` is the lower ternary code of `R_c`. The Lean theorem
`forcedRuleCCoefficient_eq_sideCoefficient` checks this identity for every tail word. This is
not prefixing one physical `c`, whose role would still depend on the tail phase.

Use prefixes and suffixes

```text
P = (ε,b,bb,btb),       Q = (ε,b,bb,bt).
```

Write `s=3^β`, `p=3s`, `a=9s`, and `u=3m+2`, with `m` the Neary marker value. Exact coordinate
calculation gives reachable and observable matrices with

```text
det R = 576a(x+1)(x+2)(2a+u−2),
det O = 76ap(p−9).
```

Both are nonzero for `β≥3`. The paired toggle `T` has determinant `−1`; hence the inserted
Hankel section

```text
H_t[p,q] = h(p t q) = (R T O)[p,q]
```

is nonsingular. Thus absorbing `R_c` does not reduce the exact paired-tail state requirement:
the phase state remains essential and `h` has rank at least four.

## Probe Domain

All sixteen words `p t q`, for `p∈P` and `q∈Q`, lie in the exact paired-companion domain used by
`MM-M01` and the surviving `MM-O16` proposal. Every nonempty prefix ends in data, every nonempty
suffix begins in data, the internal toggle of `btb` is data-flanked, and the terminal toggle of
`bt` follows data. The inserted toggle is therefore isolated, and no probe contains adjacent
toggles. The obstruction does not smuggle malformed `S²` or `S³` words into its hypotheses.

## Five-Channel Factorization

Let an arbitrary five-state physical family have toggle `S`, two-channel output `V`, and
two-channel input `U`. Assume that on the sixteen probes it exactly realizes

```text
V A_{ptq} U = diag(λh(ptq),1),       λ≠0.             (1)
```

Select four active reach rows and columns from `P,Q`, then add the constant output and input
channels. Equation (1), including its zero cross channels, assembles into

```text
R₅ S O₅ = diag(λH_t,1).                              (2)
```

The determinant of the right side is `λ⁴ det(H_t)`, which is nonzero. Therefore `det S≠0`.
Consequently `S³` is invertible and has rank five, contradicting the bordered delimiter
requirement `rank(S³)=2`.

The standard off-diagonal companion is covered: if

```text
J(z) = [[0,z],[1,0]],       P = [[0,1],[1,0]],
```

then `J(z)P=diag(z,1)`. Changing the input-channel basis by `P` converts an exact `MM-M01`
realization into (1). The theorem imposes no form on the physical data matrices, so nonzero
fifth-coordinate couplings cannot evade it.

## Boundary

The result requires exact joint realization of the derivative and constant channels on the
displayed probes. It does not require universal rejection of odd words, nonsingular controls,
or a wordwise converse beyond that finite exact domain. It does not obstruct a changed series
with the same existential zero behavior.

The live `M₅(3)` routes are therefore unchanged outside the killed leaf: the setter/projective
route, a weaker same-zero or existence-only scalar compiler, and the scheduled source compiler
all survive. A genuine square/cube grammar could still belong to one of those changed-series
constructions; it cannot repair this exact companion.

## Formal Artifact

[`MatrixMortality/ForcedRuleCCompanion.lean`](../MatrixMortality/ForcedRuleCCompanion.lean)
checks:

- the semantic `R_c` derivative identity;
- both determinant formulas and their nonvanishing;
- the inserted-toggle Hankel factorization and rational cast;
- the five-channel probe factorization;
- physical-toggle invertibility; and
- the contradiction with `rank(S³)=2`.

The principal declarations are `forcedRuleCCoefficient_eq_sideCoefficient`,
`forcedRuleCInsertedHankelRat_det_ne_zero`, `forcedRuleC_exact_state_lower_bound`,
`forcedRuleCCompanion_probe_factor`, `exactForcedRuleCCompanion_toggle_det_ne_zero`, and
`exactForcedRuleCOffDiagonalCompanion_not_rankTwoCube`.
