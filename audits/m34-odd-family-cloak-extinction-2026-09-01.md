# M₃(4) Odd-Family One-Sided Cloak Extinction Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `057ee89` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeOddFamilyCloakNoGo.lean`](../MatrixMortality/MixedPrimeOddFamilyCloakNoGo.lean)
**Certificate:**
[`certify_mixed_prime_odd_cloaks.py`](../tools/certify_mixed_prime_odd_cloaks.py)

## Verdict

The explicit odd mixed-prime kernel family from `G3-S21` is globally impossible in both
one-sided cloak orientations. This includes both assignments of the relation sides to the flat
and nested physical fork words.

For a prefix cloak, the formal `G3-S23` gate supplies nonempty equal-length cloak suffixes with
equal Parikh vectors. If their common length is `q`, then

```text
2(address_depth+q) < |Lₖ|.
```

The odd-family Parikh theorem proves that its sole positive proper balanced suffix has
`q=|Lₖ|-3`. Since `|Lₖ|=29+2k`, the two inequalities are incompatible at every pump and address
depth. Lean proves the forward and reversed orientations separately.

For a suffix cloak, an accepting factorization would have

```text
yzxyx=W·Lₖ,       xzyxy=W·Rₖ,
```

where `W` is an aligned `{DT,TD}` address. Internal trigrams cancel on each side. The physical
five-block fork has exactly `1,243` boundary discrepancy vectors, while the address contributes
only the junction contexts `ε`, `DT`, and `TD`. All three odd-family target vectors, and their
negatives under reversed orientation, miss the physical catalogue.

## All-Depth Argument

The formal factorization is

```text
Lₖ=oddFamilyLeftHead·(DT)ᵏ·DTDD,
Rₖ=oddFamilyRightHead·(DT)ᵏ·DDTT.
```

At factor length three, adding one `DT` period contributes the same internal factors to both
words and preserves the pump-tail junction after one period. In this family the depth-zero and
positive-depth signatures already coincide. Thus three address contexts in two orientations
give six distinct signatures; representing depth zero and the stable positive-depth cell yields
the certificate's twelve audited cells. Replays through depth eight check the locality
calculation but are not a cutoff.

The canonical payload digest is

```text
8a3e8605496a99e0f9eb64961084bd2b1739694c15883dec7f26d42b24ca3935
```

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every physical odd-family prefix cloak exposes a balanced suffix of length `|Lₖ|-3` | promotion | Lean composition of `G3-S23` with the odd-family Parikh theorem |
| Either relation orientation realizes a prefix-cloaked exact endpoint | rejected | two Lean no-go theorems |
| The odd family has only one suffix-cloak trigram cell per address context | promotion | exact two-letter pump locality |
| Either relation orientation realizes a suffix-cloaked physical fork | rejected | complete `1,243`-signature certificate |
| Any discovered mixed-prime kernel relation admits a one-sided cloak | open | result covers the odd family and the 23 `G3-S16` schemas only |
| Interleaved addresses or separate two-offset routing are impossible | open | outside the one-sided equations |
| `M₃(4)` follows | rejected | other kernel relations, interleaving, routing, and the endpoint converse remain |

## Master Delta

```text
DEAD: the explicit infinite odd kernel family in both one-sided cloak orientations.
COMBINED: every currently explicit infinite mixed-prime kernel family is dead as a one-sided cloak.
LIVE: undiscovered kernel relations, interleaving, separate two-offset routing, and converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, Lean LSP
diagnostics, exact symbolic certificate, Ruff, ty, and forbidden-aperture scan pass.
