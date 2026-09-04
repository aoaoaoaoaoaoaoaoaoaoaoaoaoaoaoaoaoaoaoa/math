# M₃(4) Suffix-Cloak Factor-Boundary Collapse Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `2190d25` on `wave3-m34-transverse`
**Formal reduced fork:**
[`GuardedMixedPrimeReducedKernel.lean`](../MatrixMortality/GuardedMixedPrimeReducedKernel.lean)
**Certificate:**
[`certify_mixed_prime_suffix_factor_boundaries.py`](../tools/certify_mixed_prime_suffix_factor_boundaries.py)

## Verdict

All `23` Cayley–Hamilton pump schemas are also globally impossible in the suffix-cloak orientation.
Together with `G3-S24`, this closes both one-sided address-cloak realizations of the entire
`G3-S16` family.

Suppose an accepting equal-address instance had the physical raw form

```text
yzxyx=W·Lₖ,       xzyxy=W·Rₖ,
```

where `W` is an aligned `{DT,TD}` address and `Lₖ,Rₖ` are one of the equal-action pump pairs.
Count all contiguous trigrams. On the physical side, internal factors of `x,y,z` cancel because
the two words contain the blocks with the same multiplicities. Only the four block boundaries
remain. Exact enumeration of the binary boundary types gives `1,243` possible physical trigram
discrepancy vectors.

On the cloak side, factors internal to `W` cancel. Trigrams crossing `W|Lₖ` or `W|Rₖ` depend only
on the last two letters of `W`. There are exactly three cases:

```text
W=ε,       last₂(W)=DT,       last₂(W)=TD.
```

Every nonempty aligned address ends in one complete macro, so no fourth context exists. For each
of the `23` schemas and all three contexts, the target trigram discrepancy lies outside the
physical catalogue.

## All-Depth Argument

Each cloak has form `A·Pᵏ·B` with `P∈{DT,TD}`. Pump depth zero is the sole preperiod. From
`k=1` onward the pump segment already contains the two letters seen by a trigram boundary.
Increasing `k` by one inserts a full alternating period. It adds the same internal trigram
multiset on both cloak branches and preserves both junction contexts, so every contextual
discrepancy is constant for all `k≥1`.

The certificate therefore checks exactly six cells per family: three address contexts at `k=0`
and the same three in the stable `k≥1` cell. It replays powers `2` through `8` to audit the local
stability equation; this replay is not a cutoff. The canonical payload digest is

```text
35b5c03c65c53697cbba542c989446c44e8a89b2a87feb7d2710d40523ab3e0f
```

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Physical reduced forks have one of `1,243` trigram boundary discrepancies | promotion | exact finite boundary catalogue |
| A nonempty aligned prefix has only `DT/TD` trigram boundary contexts | promotion | literal macro grammar |
| Every pump cloak has only a depth-zero and stable positive-depth signature | promotion | exact two-letter locality |
| Any of the 23 pump schemas realizes a suffix-cloaked fork | rejected | complete symbolic certificate |
| Either one-sided cloak orientation works for one of the 23 schemas | rejected | `G3-S24` plus this result |
| The odd kernel family or another relation fails both orientations | open | outside the 23-family census |
| Interleaved addresses or two-offset routing are impossible | open | outside the one-sided equations |
| `M₃(4)` follows | rejected | other carriers and the endpoint converse remain |

## Master Delta

```text
DEAD: all 23 Cayley–Hamilton pump schemas in suffix orientation, at every depth.
COMBINED: all 23 are dead in both prefix and suffix cloak orientations.
LIVE: odd/other kernels, interleaving, two-offset routing, and arbitrary-word converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The exact symbolic certificate, complete `1,243`-signature boundary catalogue, pump-stability
replay, Ruff, ty, and the repository's decomposed strict gates pass.
