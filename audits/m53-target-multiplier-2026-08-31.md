# Primitive Target Multiplier Braid Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** a primitive full-tail pole has one unique unit target multiplier; its literal prefix
discrepancy braids directly to the initial predecessor cylinder and leaves exactly two terminal
residue arms

## Multiplier

For a target ending in `β` erasures, the punctuated upper and lower codes factor as

```text
P=3^β(U+1)−1,       V=3^β(L+1)−1.
```

If the final carrier `(n₂,d₂)` is primitive and satisfies `d₂P=n₂V`, Bézout cancellation gives
a unique integer `λ` with `P=λn₂` and `V=λd₂`. The upper factorization makes `P` a unit modulo
three, hence `λ≠0` and `3∤λ`. Combining these equations with
`d₂−n₂=3^βq₂` proves the literal prefix identity `L−U=λq₂`.

Substitution into the `MM-S73` charge braid gives

```text
u₀u₁u₂(L−U)=−2μHλ(2μk₀+u₀d₀).
```

Lean proves equivalent divisibility by `3^h` for every `h` and equal integer three-adic
valuations on the two exposed factors.

## First Mismatch

The upper discarded prefix ends in `true`. The lower prefix is empty or its spelling ends in
`false`. Together with primitive final coordinates, this proves `3∤q₂`; the exact charge chain
then proves the preceding numerator charge and middle affine charge are also units. Consequently
the literal prefix discrepancy and predecessor braid residual are units.

Using both singleton `D_c` denominator equations and the initial physical role-block denominator
equation pulls the terminal digit back to

```text
front=[]       => 3 ∣ k₀,
front≠[]       => k₀ ≡ e₋₁ (mod 3).
```

Exact width-three search found the required carrier residue pattern on reachable local chains in
both arms. This is a no-go for a block-local residue extinction, not evidence of a pole. In the
empty arm Lean proves the sharper identity `3^β−1=λd₂`, hence `λ∣(3^β−1)` and
`|d₂|≤3^β−1`. Exact width-three classification leaves all eight erasure targets and every tested
preceding local role block. The nonempty arm retains longer prefix ancestry.

## Boundary

The target must end in a full `β`-erasure tail and the three-block physical normalization data
must be explicit. The multiplier theorem itself is independent of the preceding history. The
residue pullback requires `β≥2` and all three denominator equations. No arbitrary-target or
`M₅(3)` conclusion follows.

## Verification

[`SwappedSetterTargetMultiplier.lean`](../MatrixMortality/SwappedSetterTargetMultiplier.lean)
and
[`SwappedSetterTargetResidue.lean`](../MatrixMortality/SwappedSetterTargetResidue.lean)
contain the checked results. Both modules build warning-free; their namespaces pass the default
linters; LSP reports no diagnostics; and every public theorem is listed in `AxiomAudit.lean`.

## Artifacts

- [`MM-S73`](../SALVAGE.md#mm-s73-live-three-block-charge-frontier)
- [`MM-S76`](../SALVAGE.md#mm-s76-primitive-target-multiplier-braid)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
