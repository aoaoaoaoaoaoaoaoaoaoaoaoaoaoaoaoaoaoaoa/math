# M₃(4) Aligned-Address Fork No-Go Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `a44093b` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeAddressForkNoGo.lean`](../MatrixMortality/MixedPrimeAddressForkNoGo.lean)

## Verdict

The exact comparator of `G3-S18` cannot be installed by keeping the complete forced `bcbc` fork
inside the aligned `{DT,TD}` address submonoid. Exact endpoint semantics forces the flat and
nested fork words to be distinct while inducing the same affine action. Evaluation at zero is
injective on aligned addresses of arbitrary length. Hence the two fork words cannot both be
aligned addresses.

In particular, assigning each of the three fixed paired controls a whole aligned address is
impossible. Some control boundary must break the two-letter address phase. Even if the toggle is
allowed to be arbitrary and unaligned, the two data controls cannot be equal-length aligned
addresses: their slopes would agree, while exact endpoint semantics forces unequal data slopes.

This is a carrier obstruction, not a rejection of every use of the address mechanism. An aligned
address may still occur as an interior segment of a larger fork word outside the address
submonoid, or its scalar offset may be routed through a separate endpoint interface.

## Forced Collision

Let `κ` be a raw mixed-prime block code. Existing formal results for the fixed `bcbc` source give

```text
F = κ*(flatForkControl),       N = κ*(nestedForkControl),
F ≠ N,                        wordAction(F)=wordAction(N).
```

Suppose there are binary addresses `u,v` with

```text
F=expandAddress(u),       N=expandAddress(v).
```

Evaluating the forced action equality at zero and applying `G3-S18` yields `u=v`. Expansion then
gives `F=N`, contradicting the genuine-kernel theorem. No equal-length premise is used: the
five-adic scalar code recovers address depth as well as content.

Lean states this as `no_bcbc_endpoint_of_fork_address_words`. It assumes only the two displayed
address representations and the complete endpoint equivalence. The individual control macros
need not themselves be aligned.

## Aligned Codes

Lean proves the exact monoid law

```text
expandAddress(u·v)=expandAddress(u)·expandAddress(v).
```

Consequently, if each control has a binary macro address `a(x)` and

```text
κ(x)=expandAddress(a(x)),
```

then every encoded control word is the aligned address obtained by concatenating its control
addresses. Both forced fork branches therefore lie in the aligned submonoid, and the preceding
collision argument rejects the code. This allows empty control addresses and unequal address
lengths; neither is an escape.

The second corollary needs less alignment. If only

```text
κ(b)=expandAddress(u),       κ(c)=expandAddress(v),       |u|=|v|,
```

then both data slopes are `(2/5)^|u|`. The formal unequal-slope theorem for every exact endpoint
code gives an immediate contradiction, regardless of `κ(toggle)`.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Address expansion preserves concatenation | promotion | Lean induction |
| A controlwise aligned code maps every word to one concatenated address | promotion | Lean induction |
| Both forced fork words may lie in the aligned address submonoid | rejected | scalar injectivity versus genuine kernel |
| All three fixed controls may be coded by whole addresses | rejected | formal corollary |
| Equal-length aligned data macros are possible with an unaligned toggle | rejected | exact unequal-slope theorem |
| One interior address segment inside a globally unaligned fork is impossible | open | outside the hypotheses |
| A separate two-offset terminal reader is impossible | open | outside the hypotheses |
| `M₃(4)` follows | rejected | dynamic production, routing, and malformed-word converse remain |

## Master Delta

```text
DEAD: the complete forced fork inside the aligned address submonoid.
DEAD: three controlwise aligned address macros, at arbitrary lengths.
DEAD: equal-length aligned b/c macros, even with arbitrary toggle.
MANDATORY ESCAPE: break address phase around the global fork, or read interior offsets separately.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, and forbidden-aperture scan pass. The formal source SHA-256 is

```text
c1d98f7a978f38c8fef08722bd72619244a5676338f28f1251f0e45f360dbe76  MixedPrimeAddressForkNoGo.lean
```
