# Swapped Positive Depth-One Extinction

**Date:** 2026-08-31
**Target:** the valuation-one pole after one positive distinguished-boundary transfer in the
swapped ternary setter
**Verdict:** closed at the exact fringe-witness interface

## Statement

Put

```text
ρ=3^β,       μ=2ρ−1,       D=ρ−2,       H=5ρ−1.
```

For a preceding unmatched fringe pair `(A,B)` and prospective Neary word with swapped upper and
lower codes `(P,V)`, the exact valuation-one pole equation is

```text
ΔDP=H(3μ−Δ)V,       Δ=[A]₃−[B]₃.
```

If `β≥6`, the regular upper, source, and target fringe languages together with the pole
congruence leave exactly four pairs:

```text
(111·0^(β−1), ε),       Δ=14·3^(β−1)−1,
(11·0^β, ε),            Δ=H,
(tag_b, 0^β),           Δ=H,
(tag_b, 0^(β−1)),       Δ=17·3^(β−1)−1.
```

The first and fourth pairs decode to the two stable nonterminal residuals. Their Neary histories
have adjacent lengths modulo `β−1`, so neither can occur when `β−1` divides the compiler body
length. In either middle pair, `Δ=H`; since `D+H=3μ`, the exact pole equation becomes

```text
DHP=DHV.
```

Both factors are nonzero, hence `P=V`. Injectivity of the swapped ternary code turns this into a
genuine Neary terminal match and therefore a halting source computation.

## Formalization

[`SwappedSetterPositiveDepthOne.lean`](../MatrixMortality/SwappedSetterPositiveDepthOne.lean)
defines the exact pole and its witness interface. The public declarations are:

- `poleCongruence_four_fringe_pairs`, the four-way classification;
- `positiveDepthOnePoleWitness_halts`, the complete residual-or-terminal elimination;
- `compilerPositiveDepthOnePoleWitness_halts`, its compiler-emitted specialization.

The emitted compiler uses `β=10·period`; a positive period therefore gives `β≥10`, strictly
inside the analytic threshold. The compiler arithmetic envelope supplies body length, divisibility,
and the initial queue used by the conclusion.

Direct Lean elaboration, the default environment linters, and transitive axiom inspection pass.
Each public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Scope

This module closes one transfer from the distinguished boundary into a valuation-one target
pole. Its witness does not classify the singleton `β`-shell or identify a later multi-transfer
carrier with the raw fringe witness. The former is now closed independently by `MM-S08`; the
first genuinely multi-transfer branches remain outside this result.

The compiler theorem consumes an assembled `PositiveDepthOnePoleWitness`; it does not construct
that witness from an arbitrary raw projective orbit. In particular, `targetSuffix_eq` records the
physical provenance of the bounded target suffix on the witness side. Once `targetFringe` and
`poleCongruence` have been supplied, the extinction proof does not reconstruct or otherwise use
that equality.

## Master Delta

The positive depth-one fringe search is finished. Future attacks must begin at the multi-transfer
carrier, not refine the four stable fringe candidates or repeat bounded suffix enumeration.
