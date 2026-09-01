# M₃(4) Common Address-Wrapper No-Go Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `b81bf11` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeAddressWrapperNoGo.lean`](../MatrixMortality/MixedPrimeAddressWrapperNoGo.lean)

## Verdict

A shared phase-breaking wrapper does not rescue the aligned address comparator. Suppose the two
forced `bcbc` fork words have the form

```text
P·expandAddress(u)·Q,       P·expandAddress(v)·Q.
```

The fixed raw contexts `P,Q` may be nonempty, unaligned, and source-dependent; the addresses may
have different lengths. Exact endpoint semantics is impossible.

Every mixed-prime word action is bijective. The common prefix and suffix therefore cancel from
the forced action equality. `G3-S18` then identifies `u` and `v` from one scalar value. Restoring
the literal common contexts makes the full fork words equal, contradicting the genuine-kernel
obligation.

Thus the route left by `G3-S19` must use genuinely asymmetric or noncancellable wrappers, or a
separate terminal channel. Merely prefixing or suffixing the address comparison to disturb its
two-letter phase is dead.

## Formal Chain

Existing endpoint rigidity supplies distinct raw words `F,N` with identical affine actions. The
new theorem assumes

```text
F=P·expandAddress(u)·Q,       N=P·expandAddress(v)·Q.
```

From action equality and `wordAction_cancel_context`, Lean obtains

```text
wordAction(expandAddress(u)) = wordAction(expandAddress(v)).
```

Evaluation at zero and global address injectivity give `u=v`. The two displayed factorizations
then give `F=N`, contradicting the formal endpoint kernel pair. Empty `P`, empty `Q`, and empty
addresses are included.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| A common literal two-sided wrapper around aligned addresses can realize the forced fork | rejected | Lean cancellation and scalar injectivity |
| A one-sided common prefix or suffix can realize it | rejected | specialization with the other context empty |
| Unequal address lengths evade the obstruction | rejected | global scalar decoder includes length |
| Distinct or action-inequivalent wrappers are impossible | open | outside the hypotheses |
| A separate two-offset endpoint channel is impossible | open | outside the hypotheses |
| `M₃(4)` follows | rejected | asymmetric routing and arbitrary-word converse remain |

## Master Delta

```text
DEAD: P·address(u)·Q versus P·address(v)·Q for any common literal P,Q.
MANDATORY ESCAPE: asymmetric/noncancellable wrappers, or a separate two-offset channel.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, and forbidden-aperture scan pass. The formal source SHA-256 is

```text
becf6d562be244d329fc418518dc17d4edee670660a797940bcf2325cf018891  MixedPrimeAddressWrapperNoGo.lean
```
