# Paired Inverse-Chamber Audit

**Date:** 2026-08-10  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `30d04f499903128daa9a322a69d529aa6dffb9ae` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a796385-0238-83ea-9346-044c3f9dc3ee

## Verdict

The report does not settle `M₃(4)` or prove a same-zero dimension lower bound. It does kill the
paired residual-saturation leaf uniformly. Two formal inverse states required by the independent
left and right free factors have positive forward cones disjoint from every actual paired suffix
and phase-aware prefix residual.

The complete chamber and forward-cone argument is kernel-checked. The report's auxiliary choice
of one halting universal-family member is unnecessary: the disjointness theorem holds for every
body and every positive deletion width, whether or not that instance halts.

## Checked Chamber Classification

Write `P={x,z}*` inside the binary free group. Lean proves that arbitrary free reduction preserves
the one-turn forms

```text
PP⁻¹: positive letters followed by negative letters,
P⁻¹P: negative letters followed by positive letters.
```

The repository's exact residual definitions then give

```text
suffixResidual β body suffix ∈ PP⁻¹,
prefixResidual β body context phase ∈ P⁻¹P.
```

This is an all-control-word statement. It uses the phase-aware decoder already proved in
`CancellativeProjectiveNoGo.lean`, so malformed and toggle-only controls are included.

## Checked Formal Inverse States

The role fractions previously isolated as `leftSeed`, `leftConjugate`, `rightSeed`, and
`rightConjugate` generate

```text
ξ_L = x⁻ᵝ z xᵝ z⁻¹,
ξ_R = x z⁻² x⁻¹ z².
```

Lean proves both the reduced signed words and their exact equality to the relevant formal inverse
combinations. When `β>0`, each word contains a negative-to-positive and a
positive-to-negative transition, hence lies outside both residual chambers.

## Checked Forward-Cone Separation

Every Neary upper role word ends in `z`; every lower role word ends in `x`, including the
`R_c` word for an empty body. For a nonempty role sequence, therefore, `U` ends in `z` and
`V⁻¹` begins in `x⁻¹`. Those letters cannot cancel the `x`-boundary and `z`-boundary of either
seed. Empty role sequences leave the seed unchanged.

Lean proves the resulting raw continuation is freely reduced and still contains the complete
seed as an infix. Consequently, for every role sequence `w`, suffix `s`, prefix `p`, and phase
`θ`,

```text
U(w) ξ_L V(w)⁻¹ ≠ suffixResidual β body s,
U(w) ξ_L V(w)⁻¹ ≠ prefixResidual β body p θ,
U(w) ξ_R V(w)⁻¹ ≠ suffixResidual β body s,
U(w) ξ_R V(w)⁻¹ ≠ prefixResidual β body p θ.
```

This is stronger than failure of direct representation: neither seed has a positive common
future with any residual represented by the paired grammar.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every paired suffix residual has at most the `+−` sign turn | promotion | `suffixResidual_positiveNegative` |
| Every phase-aware prefix residual has at most the `−+` sign turn | promotion | `prefixResidual_negativePositive` |
| `ξ_L` and `ξ_R` are the advertised formal inverse combinations | promotion | `leftInverseState_eq_formalCombination`, `rightInverseState_eq_formalCombination` |
| Both seeds lie outside both one-turn chambers | promotion | four `not_*` theorems |
| Every positive Neary context preserves both seed turns | promotion | `leftContinuation_outsideChambers`, `rightContinuation_outsideChambers` |
| Both complete forward cones miss every actual residual | promotion | four `RoleContinuation_ne_*Residual` theorems |
| Backward cancellation plus grammar structure forces inverse saturation | rejected | the explicit forward-cone separation refutes cofinality |
| A representation-specific faithful projective Ore completion is impossible | rejected | extra projective points and incidences are not fixed by the language |
| The paired zero language has same-zero dimension at least four | rejected | no one-sided transition-diagram obstruction is supplied |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: paired residual saturation and every grammar-intrinsic Ore/common-future completion.
CLOSED: the proposed route from backward cancellation to the inverse-saturated G3-O05 tax.
REMAINS: a positive one-sided projective transition-diagram lower bound, or a uniform singular
         three-state constructor which exploits precisely the absent inverse component.
```

## Artifact

- [`PairedInverseChamber.lean`](../MatrixMortality/PairedInverseChamber.lean)
