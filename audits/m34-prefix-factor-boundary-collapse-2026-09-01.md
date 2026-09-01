# M₃(4) Prefix-Cloak Factor-Boundary Collapse Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `1dac558` on `wave3-m34-transverse`
**Formal reduction:**
[`MixedPrimePrefixPumpSuffixNoGo.lean`](../MatrixMortality/MixedPrimePrefixPumpSuffixNoGo.lean)
**Certificate:**
[`certify_mixed_prime_prefix_factor_boundaries.py`](../tools/certify_mixed_prime_prefix_factor_boundaries.py)

## Verdict

All `23` Cayley–Hamilton pump schemas from `G3-S16` are globally impossible as physical
prefix-cloaked address forks. `G3-S23` killed twelve by suffix Parikh data. The eleven survivors
all fail a second local invariant on the complementary cloak heads.

After deleting the balanced terminal suffixes, Lean's formal factorization gives

```text
head(Lₖ)=yzx,       head(Rₖ)=xzy,
```

with nonempty `x,y,z`. For any factor length `r`, the internal length-`r` factors of `x,y,z`
occur once on both sides and cancel. The factor-count discrepancy therefore comes entirely from
the two block boundaries. Each head has at most `2(r-1)` crossing factors, so the ℓ¹ norm of the
difference is at most `4(r-1)`.

At `r=2`, this bound is `4`. The complete eventually periodic head signatures of six families
have norms from `8` to `16`, killing

```text
l31-01  l31-02  l31-04  l32-06  l32-07  l32-15.
```

At `r=3`, the bound is `8`. Four more families have signature norms from `10` to `22`, killing

```text
l31-06  l32-02  l32-08  l32-13.
```

The final family `l32-05` attains the norm bound but still fails the exact boundary catalogue.
Its bigram discrepancy forces the endpoint pattern

```text
first/last(x)=T/D,    first/last(y)=D/T,    first/last(z)=T/T.
```

Both boundaries of `yzx` therefore contain `TT`, so no crossing trigram can be `DDD`. Yet each of
the two possible head signatures has `DDD` discrepancy `+1`. This is impossible. The certificate
also verifies the conclusion directly against all `1,203` realizable trigram boundary signatures.

## Exact Catalogue

For length `r`, a nonempty block's contribution to crossing factors is determined by the whole
block when it has length below `2(r-1)`, and otherwise by its first and last `r-1` letters. Thus
there are only six binary boundary types at `r=2` and thirty at `r=3`. Exact enumeration of all
triples gives

```text
21 possible bigram discrepancy vectors,
1,203 possible trigram discrepancy vectors.
```

The pump-head side is also finite symbolically. Before the `G3-S23` stabilization power, every
balanced feasible suffix is replayed directly. Afterwards, short fixed suffixes have one stable
signature. Longer suffixes depend only on `t=2k-q`; once the remaining alternating pump segment
exceeds the factor radius, increasing `t` by two adds one full `DT` or `TD` period to both heads
and leaves the discrepancy fixed. The certificate enumerates the finite short residues and one
stable cell for each balanced parity. A depth-`50` replay checks the cell decomposition but is not
the all-depth argument.

The canonical payload digest is

```text
35d310b36c0a73527328951913f90d941e1ed5a00a6792d5e76d82f111074601
```

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A physical prefix cloak has complementary heads `yzx,xzy` | promotion | Lean `G3-S23` factorization |
| Its length-`r` factor discrepancy is boundary-local with norm at most `4(r-1)` | promotion | exact finite-word argument |
| Six surviving pump families violate the bigram boundary budget globally | promotion | symbolic periodic certificate |
| Four more violate the trigram boundary budget globally | promotion | symbolic periodic certificate |
| `l32-05` realizes an admissible trigram boundary type | rejected | unique endpoint contradiction and exact catalogue |
| Any of the 23 pump schemas realizes a prefix-cloaked fork | rejected | `G3-S23` plus this complete certificate |
| Every possible mixed-prime kernel cloak fails in prefix orientation | open | odd and undiscovered kernel families lie outside the census |
| A suffix cloak or separate two-offset channel is impossible | open | outside the theorem |
| `M₃(4)` follows | rejected | other cloak families, orientations, and endpoint converse remain |

## Master Delta

```text
DEAD: the complete 23-family Cayley–Hamilton pump prefix-cloak line, at every depth.
NO SURVIVOR: six bigram deaths, five trigram deaths after the twelve Parikh deaths.
LIVE: odd/other kernel cloaks, suffix orientation, interleaving, two-offset routing, converse.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The formal head reduction was already warning-free and axiom-audited in `G3-S23`. The new exact
symbolic certificate, its periodic cell replay, Ruff, ty, and the repository's decomposed strict
gates pass.
