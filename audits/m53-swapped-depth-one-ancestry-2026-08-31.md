# Swapped Depth-One Ancestry Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the post-`D_c²` carrier does not admit an unconditional integral raw-fringe splice

[`MM-S50`](../SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction) leaves one expected-shell
first multi-transfer shape: literal `D_c²` before a depth-one target. The positive depth-one
classifier [`MM-S42`](../SALVAGE.md#mm-s42-swapped-positive-depth-one-extinction) instead consumes
an integer difference of raw swapped ternary codes. This audit determines the exact algebraic
interface and tests whether the shell shape supplies it.

## Exact Normalization

Put `ρ=3^β`, `μ=2ρ−1`, `H=5ρ−1`, and `R=2−ρ`. A physical first role block has upper length
`m`, punctuated upper code `P`, and centered state

```text
(X₁,Y₁)=(3^m,RP).
```

The literal middle `D_c²` has upper length two, lower code eight, punctuated upper code
`14ρ−1`, and centered coefficient

```text
C₂=R(14ρ−1)−8H.
```

Applying the centered recurrence and normalizing by `−3Y/((ρ−2)X)` gives

```text
δ=(C₂P+8Hμ·3^m)/(3RP).                                 (1)
```

Lean proves (1) from the physical `nextX` and `nextY` definitions; it is not an abstract ratio
substitution.

## Integrality Gate

Suppose `δ=z∈ℤ`. Clearing the nonzero denominator in (1) shows

```text
P ∣ 8Hμ·3^m.                                            (2)
```

Every physical punctuated upper code is congruent to two modulo three. Hence `gcd(P,3^m)=1`, and
(2) contracts to the body- and length-independent gate

```text
P ∣ 8Hμ.                                                (3)
```

No sign or positivity assumption is used in this cancellation.

## Physical Recurrence Counterexample

Choose the physical first role block to be `D_c²` as well. Then `m=2` and `P=14ρ−1`. If (3)
held, the polynomial identity

```text
196·8Hμ − (1120ρ−704)(14ρ−1)=864                        (4)
```

would make `14ρ−1` divide `864`. For `β≥4`, this positive divisor exceeds `864`. Lean checks
`β=3` directly. Therefore this repeated-`D_c²` state has nonintegral normalization at every
admissible width. It cannot equal any difference of raw swapped ternary codes, including the
discrepancy field of a `PositiveDepthOnePoleWitness`.

The first block in this counterexample is a literal lawful role block and the state is produced
by the centered physical recurrence. It is not proved reachable from the distinguished compiler
entry, and it need not itself be a preceding pole. The result therefore refutes a local adapter
whose hypotheses are only the role-block recurrence and `D_c²→depth-one` shell. It does not
exclude a stronger orbit-specific ancestry theorem.

## Exact Pole Bridge

For any rational carrier `(X,Y)` with `((ρ−2)X)≠0`, Lean proves that normalization to an arbitrary
rational `δ` turns the physical next-block pole equation exactly into

```text
δ(ρ−2)P_t = H(3μ−δ)V_t.                                (5)
```

When `δ=z∈ℤ`, exact casting identifies (5) with `PositiveDepthOnePole β body z targetWord`.
There is no width hypothesis beyond the stated denominator nonvanishing. This proves that no
second algebraic pole obligation is hidden after integrality. A full
`PositiveDepthOnePoleWitness` still requires the raw prefix factorizations, fringe-language
memberships, target suffix identity, and pole congruence.

## Scope

`MM-S52` does not kill the actual `D_c²` first multi-transfer survivor and does not claim that the
repeated state is a compiler orbit. Its contribution is negative and exact: expected shell data
cannot justify importing `MM-S42`. The direct rational ratio-cylinder exclusion is a separate
`MM-S51` result.

## Verification

[`SwappedSetterDepthOneAncestry.lean`](../MatrixMortality/SwappedSetterDepthOneAncestry.lean)
contains the exact code identities, formula (1), the two divisibility gates, the repeated-state
nonintegrality theorem, both raw-code corollaries, and the rational and integral pole bridges.
The module builds without warnings. Its namespace passes the default environment linters, and
`AxiomAudit.lean` records the publication-facing transitive axiom sets.

## Artifacts

- [`SwappedSetterDepthOneAncestry.lean`](../MatrixMortality/SwappedSetterDepthOneAncestry.lean)
- [`MM-S42`](../SALVAGE.md#mm-s42-swapped-positive-depth-one-extinction)
- [`MM-S50`](../SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction)
- [`MM-S52`](../SALVAGE.md#mm-s52-double-deletion-raw-ancestry-obstruction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
