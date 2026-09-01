# M₃(4) Pumped Prefix-Cloak Suffix Collapse Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `94e5613` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimePrefixPumpSuffixNoGo.lean`](../MatrixMortality/MixedPrimePrefixPumpSuffixNoGo.lean)
**Certificate:**
[`certify_mixed_prime_prefix_pump_suffixes.py`](../tools/certify_mixed_prime_prefix_pump_suffixes.py)

## Verdict

The terminal overlap from `G3-S22` yields an exact pump-family sieve. In any physical
prefix-cloaked factorization, let `q` be the positive number of cloak letters retained inside the
terminal data blocks after deleting the common address suffix. Lean proves that the two retained
cloak suffixes have equal length `q`, equal `D/T` Parikh vectors, and satisfy

```text
2(address_depth+q) < cloak_length.
```

This kills `11` of the `23` pump families uniformly at every pump depth: no suffix satisfying the
size gate has equal Parikh data. A twelfth family, `l32-12`, has one preperiodic balanced suffix
`q=2k+5` for `0≤k≤10`; exact physical-factor replay rejects all `2,288` resulting geometries in
both branch orientations. At `k≥11`, every feasible suffix lies inside the periodic pump-tail
region, where its `D`-count discrepancy is constantly `-1`. Thus `l32-12` also dies globally.

Exactly `11` prefix-cloak pump families survive this theorem:

```text
l31-01  l31-02  l31-04  l31-06
l32-02  l32-05  l32-06  l32-07  l32-08  l32-13  l32-15
```

No physical factorization has been found in those families through pump depth `20`, but that
cutoff is not promoted. Their periodic balanced-suffix ladders are genuine and require a stronger
word-equation invariant.

## Formal Gate

Write

```text
yzxyx = L·expandAddress(u),       xzyxy = R·expandAddress(u).
```

Since `2|u|<|x|+|y|`, the common address is a proper suffix of each terminal data pair. Free-list
comparability gives unique exposed pieces `L′,R′` with

```text
L=(yzx)L′,    yx=L′·expandAddress(u),
R=(xzy)R′,    xy=R′·expandAddress(u).
```

The pieces are nonempty. Counting lengths gives `|L′|=|R′|=q`; counting either letter and
cancelling the common address count gives `Parikh(L′)=Parikh(R′)`. Finally,

```text
2|x|+2|y|+|z| = |L|+2|u|,
|x|+|y| = q+2|u|,
```

and `|z|>0` yield `2(|u|+q)<|L|`. Lean proves this without naming any pump family.

## Periodic Certificate

Each certified relation has the form

```text
A·Pᵏ·B,       C·Pᵏ·D,
```

where `P` is `DT` or `TD`. For each family the certificate computes the first depth `K` at which
every suffix allowed by `2q<base_length+2k` remains inside both `Pᵏ·B` and `Pᵏ·D`. The
preperiod `k<K` is finite and checked exactly. Inside the periodic region, if `r` pump letters
precede a fixed tail, its number of `D`s is exactly

```text
tail_D + floor(r/2) + odd(r)·[last(P)=D].
```

The difference is therefore two-periodic in `q`. For the `11` uniform deaths it is nonzero in
both parities, and every shorter fixed-tail suffix is also unbalanced. The eliminated identifiers
are

```text
l31-03  l31-05  l31-07
l32-01  l32-03  l32-04  l32-09  l32-10  l32-11  l32-14  l32-16.
```

For `l32-12`, the same periodic argument begins at `K=11`. Its earlier balanced suffix is exactly
`2k+5`; the parity-DSU solver enumerates every positive `x,y,z`, every legal address depth, and
both branch orders. The canonical certificate digest is

```text
70c25d60b09835aa980d3922041010b7bde35cb0001c95b388f93b57baa748b2
```

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A physical prefix cloak exposes nonempty equal-length cloak suffixes | promotion | Lean list factorization |
| The exposed suffixes have equal Parikh vectors | promotion | Lean count cancellation |
| Their size satisfies `2(address_depth+q)<cloak_length` | promotion | Lean length algebra |
| Eleven named pump families fail this condition at every depth | promotion | exact symbolic periodic certificate |
| `l32-12` has a physical prefix factorization before depth `11` | rejected | complete `2,288`-geometry certificate |
| The remaining eleven families have no physical factorization | open | only a depth-`20` exploratory cutoff |
| A suffix cloak or two-offset channel is impossible | open | outside the prefix theorem |
| `M₃(4)` follows | rejected | eleven prefix families, other carriers, and converse remain |

## Master Delta

```text
GLOBAL DEATHS: 12 of the 23 pumped prefix-cloak families.
LIVE PREFIX CORE: exactly 11 periodic balanced-suffix families.
NEXT CUT: a stronger periodic word-equation invariant on those 11, not a larger depth cutoff.
OTHER SURVIVORS: suffix cloak, interleaving, separate two-offset route, and endpoint converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, exact symbolic and finite certificate replay, Ruff, ty, and
forbidden-aperture scan pass. The formal source SHA-256 is recorded after the final checked build.

```text
b7766666ef1f4430c3edd36b3604559c7454aca9fb49121c644140828f696fc0  MixedPrimePrefixPumpSuffixNoGo.lean
```
