# Transverse-History Countermodel Audit

**Date:** 2026-08-11  
**Author and formalizer:** GPT-5.6 Sol  
**Human role:** elicited by @eternalism_4eva  
**Baseline:** `8f175823b3b7a071eb73bf14ae06b17683b04b58` on
`m34-cancellative-projective-no-go`  
**External report:** https://chatgpt.com/share/6a7b3bd0-839c-83ea-b0bb-a1cf7d17908d

## Verdict

The report does not close `M₃(4)`, but its counterexample is correct and changes the transverse
branch. Distinct rank-two kernels, the bilinear fibre formula, and its exceptional locus do not
force a collision or a fourth state. One fixed integral triple encodes every decoded role history
and gives a source-computable exact recognizer for the entire minimum-body subclass.

The report's projective completion is not needed for the promoted theorem. Every actual state has
third coordinate one, so the orbit reaches neither a zero vector nor the bilinear base point.
Lean proves the stronger executable statement directly on the full free control monoid.

## Checked Construction

For role code `κ` and phase sign `ε`, the state is

```text
P(κ,ε)=(8κ−ε,4κ−ε,1)ᵀ.
```

The controls are

```text
B=[[0,8,17],[0,4,9],[0,0,1]],
C=[[8,0,25],[4,0,13],[0,0,1]],
T=[[3,−4,0],[2,−3,0],[0,0,1]].
```

Lean checks `H_yP(0,1)=P(κ(decode(y)),ε(y))` for every raw control word. The role residues
modulo four are `1,2,3,0`, proving code injectivity. For target `K`, the row
`(1,−1,−4K)` emits `4(κ−K)`. The data kernels are exactly `ℚe₁` and `ℚe₂`.

Combining this with the existing minimum-body uniqueness theorem gives

```text
λ_K H_y γ=0 ↔ pairedCoefficient(ℚ,β,body,y)=0
```

for every `y`, every `β>2`, and every `body` of length `β−1`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The mixed-radix code is injective | promotion | `TransverseHistory.code_injective` |
| The displayed matrices obey the state recurrence on every raw word | promotion | `product_mulVec_column` |
| The data kernels are distinct coordinate lines | promotion | `data_mulVec_eq_zero_iff` |
| Minimum bodies have exactly the same scalar and paired zeros | promotion | `minimalBody_zero_iff_paired_zero` |
| Exceptional fibres create an accidental terminal zero | rejected | actual states have homogeneous coordinate one |
| Distinct kernels force a fourth state | rejected | explicit integral countermodel |
| The construction handles unrestricted bodies | rejected | one terminal target code is selected |

## Master Delta

```text
MASTER VERDICT: still open.
REMOVED: a transverse-kernel no-go based only on kernel geometry, the bilinear fibre law, zero
         images, or its exceptional projective point.
SURVIVOR: an infinite terminal section or genuinely two-dimensional terminal orbit computable
          from arbitrary `(β,body)`; alternatively, a universality-specific decidability theorem.
CROSS-POLLINATION: common- and transverse-kernel fixed compilers now both exist. Uniform terminal
                   arithmetic, not local rank-two geometry, is the shared obstruction.
```

## Artifact

- [`TransverseHistory.lean`](../MatrixMortality/TransverseHistory.lean)
