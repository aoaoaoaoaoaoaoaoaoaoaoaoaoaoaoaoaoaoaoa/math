# Decimal Setter Complete Hidden-Branch Separation Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the physical first-cylinder collision pair has distinct complete same-tail branches;
any cross-tail address collision forces one exact positive-depth asymmetric suffix shell

This audit continues the generalized decimal carrier analysis after the surviving
distinguished-reset entry. It does not prove projective avoidance or settle `M₅(3)`.

## Physical Branch Difference

For one normalized block, write

```text
Ψ(y)=C/(τ−10^hEy).
```

Consider the lawful pair

```text
B_R=R_b R_c D_b,             B_D=D_b R_c D_b.
```

They have common upper code `P` and common shift `h=2β+3`. Put `V_R,V_D` for their lower
codes and `ℓ=|H(body)|`. The exact lower-code calculation from `MM-O20` is

```text
V_R−V_D=550·10^(ℓ+4),
(ν₂,ν₅)(V_R−V_D)=(ℓ+5,ℓ+6).                 (1)
```

At a common unit tail `y`, subtracting the complete branches cancels the shared `G V_R V_D`
term:

```text
Ψ_R(y)−Ψ_D(y)
 = μGE(V_R−V_D)(P−10^(h+1)y)
   / [10(τ_R−10^hEy)(τ_D−10^hEy)].          (2)
```

Every factor outside `V_R−V_D` and `10` is a decimal unit. Therefore

```text
(ν₂,ν₅)(Ψ_R(y)−Ψ_D(y))=(ℓ+4,ℓ+5).           (3)
```

The branches are pointwise distinct. If a common outer inverse word has total shift `s`, exact
inverse contraction carries (3) to `(ℓ+4+s,ℓ+5+s)`. Complete addresses with the same outer
word and later tail therefore cannot identify the two hidden phases.

## Cross-Tail Synchronization

The forward decoder is

```text
Φ(x)=(τx−C)/(10^hEx).
```

It is the exact inverse of `Ψ` on decimal units. Decoding one current unit through the two
hidden branches gives

```text
Φ_R(x)−Φ_D(x)
 = G(V_R−V_D)(x−10μ)/(10^(h+1)Ex).           (4)
```

Equations (1) and (4) yield

```text
(ν₂,ν₅)(Φ_R(x)−Φ_D(x))
  =(ℓ−2β+1,ℓ−2β+2).                          (5)
```

Backward words are injective on decimal-unit tails. Hence if two complete addresses share an
outer word, choose `B_R` and `B_D` at the next position, and nevertheless agree, stripping the
outer word and applying (5) forces exactly that shell between their later tails. Neary's emitted
body theorem gives `ℓ≥2β`; both depths in (5) are positive and their cross-prime gap is one.

## Boundary

The branch images are not proved disjoint. In fact `MM-O20` shows that their unit-domain images
have the same first cylinder. The present result says precisely how two different tails must
synchronize to exploit that overlap. It does not prove that reachable suffix carriers avoid
the shell in (5), classify other overlapping block pairs, or handle singleton-target transitions.

The next decisive theorem must intersect (5) with pairs of carrier suffixes reachable from the
encoded entry. A construction realizing (5) would instead expose the first exact branch-switch
cascade.

## Verification

`DecimalSetterSuffix.forwardCarrier_inverseCarrier` checks the forward decoder.
`inverseCarrier_sub_hasDecimalShell` and
`BackwardBlock.pullbackWord_sub_hasDecimalShell` preserve arbitrary `2`/`5` depth pairs, and
`BackwardBlock.pullbackWord_injective_of_decimalUnits` strips a common outer word.
`physicalInverseCarrier_sameUpper_sub_hasDecimalShell` and
`physicalForwardCarrier_sameUpper_sub_hasDecimalShell` prove (2)--(5).
`DecimalSetterBranchSeparation.emittedHiddenInverseBranches_pullbackWord_sub_hasDecimalShell`
and `emittedHiddenInverseBranches_pullbackWord_eq_forces_tail_sub_hasDecimalShell` discharge the
physical calibration. Narrow builds, namespace lint, language-server diagnostics, and selected
axiom audit pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterSuffix.lean`](../MatrixMortality/DecimalSetterSuffix.lean)
- [`DecimalSetterBranchSeparation.lean`](../MatrixMortality/DecimalSetterBranchSeparation.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s22-complete-hidden-branch-separation)
- [`m53-decimal-inverse-cylinder-collision-2026-08-31.md`](m53-decimal-inverse-cylinder-collision-2026-08-31.md)
