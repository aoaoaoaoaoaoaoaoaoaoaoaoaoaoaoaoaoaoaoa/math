# M₃(4) Kernel-Cloaked Address Comparator Audit

**Date:** 2026-09-01
**Author and certifier:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `24581e1` on `wave3-m34-transverse`
**Formal owner:**
[`MixedPrimeKernelCloakedAddress.lean`](../MatrixMortality/MixedPrimeKernelCloakedAddress.lean)

## Verdict

The asymmetric wrapper route left by `G3-S20` is algebraically viable. Every genuine mixed-prime
kernel pair `L≠R` with identical affine action cloaks the free address comparator:

```text
wordAction(L·address(u)) = wordAction(R·address(v))  ↔  u=v,
wordAction(address(u)·L) = wordAction(address(v)·R)  ↔  u=v.
```

In both orientations, the two raw wrapped words remain distinct for every `u,v`. Thus the cloak
simultaneously supplies the mandatory raw kernel discrepancy and an exact arbitrary-length binary
address comparison. No length clock or synchronized-depth hypothesis is needed.

Lean instantiates both orientations with every member of the explicit odd mixed-prime kernel
family. This is an actual infinite family of comparators, not a conditional interface awaiting a
kernel witness.

The result does not solve `M₃(4)`. The two cloaked branches must still be realized as the physical
flat and nested images of three fixed controls, and the resulting source-indexed endpoint code
must reject every malformed raw control word.

## Prefix Cloak

Assume

```text
L≠R,       wordAction(L)=wordAction(R).
```

If the prefix-cloaked actions agree, then for every state `t`,

```text
L(address(u)(t)) = R(address(v)(t)) = L(address(v)(t)).
```

The action of `L` is injective, so the two address actions agree. Global address injectivity gives
`u=v`. Conversely, `u=v` and equality of the cloak actions make the wrapped actions equal.

Raw equality of the wrapped words would imply action equality and hence `u=v`; right
cancellation of their now-common address suffix would then give `L=R`. Therefore the wrapped raw
words are distinct even when `u≠v`.

## Suffix Cloak

For suffix cloaks, equality reads

```text
address(u)(L(t)) = address(v)(R(t)).
```

The cloak actions agree and are surjective. Evaluating on a preimage of an arbitrary state gives
equality of the two address actions everywhere, hence `u=v`. The converse is immediate. Left
cancellation of the common cloak prefix after `u=v` proves raw distinctness.

## Concrete Family

For every `k≥0`, the existing formal mixed-prime kernel gives

```text
kernelOddFamilyLeft(k) ≠ kernelOddFamilyRight(k),
wordAction(kernelOddFamilyLeft(k)) = wordAction(kernelOddFamilyRight(k)).
```

Lean composes these two facts with the generic prefix and suffix theorems. Every `k` therefore
produces two explicit raw-distinct comparators for arbitrary finite binary addresses.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Any genuine kernel pair gives an exact prefix-cloaked address comparator | promotion | Lean injective cancellation |
| Any genuine kernel pair gives an exact suffix-cloaked address comparator | promotion | Lean surjective cancellation |
| The wrapped raw words remain distinct for every address pair | promotion | Lean action implication and list cancellation |
| Address lengths must be synchronized | rejected | global address injectivity |
| Explicit mixed-prime cloaks exist at every odd-family depth | promotion | formal concrete corollaries |
| The cloaked words factor through the physical three-control fork | open | no macro factorization supplied |
| The full endpoint language and malformed-word converse follow | open | outside the theorem |
| `M₃(4)` follows | rejected | physical realization and endpoint converse remain |

## Master Delta

```text
POSITIVE: every genuine mixed-prime kernel pair cloaks an arbitrary binary equality test.
CONCRETE: both prefix and suffix comparators exist at every odd-family pump depth.
OPEN: factor the cloaked branches through x,y,z in the physical fork, then prove the all-word gate.
MASTER VERDICT: M₃(4) remains open.
```

## Validation

The warning-as-error Lean build, whole-environment linter, reviewed axiom snapshot, full/noisy
Lean LSP diagnostics, and forbidden-aperture scan pass. The formal source SHA-256 is

```text
e0e01445dd235dc1bad5c3a6622737dfe02e3ade930030446399bf30b1a3974b  MixedPrimeKernelCloakedAddress.lean
```
