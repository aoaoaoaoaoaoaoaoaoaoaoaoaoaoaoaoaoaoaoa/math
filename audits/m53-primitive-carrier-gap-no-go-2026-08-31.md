# Primitive Carrier-Gap No-Go Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** centered reachability does not bound the primitive carrier gap below `3^β` and does
not keep a nonzero primitive gap away from divisibility by `3^β`

[`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry) proves that a target with
a full `β`-erasure tail is terminal whenever the primitive carrier satisfies
`|d−n|<3^β`. This audit tests whether that bound, or bare nondivisibility by `3^β`, follows from
the centered-history dynamics.

## Integral Lift

Put `ρ=3^β`, `μ=2ρ−1`, `H=5ρ−1`, and `R=2−ρ`. Let `(n,d)` represent the normalized defect
coordinate `q=(H/R)δ`. A physical block has upper power `A`, punctuated upper code `P`, and lower
code `V`. Clearing the Möbius denominator gives the integer successor

```text
n'=H((P−μA)d−Vn),
d'=R(Pd−Vn).                                            (1)
```

Lean proves directly from the homogeneous centered recurrence that `(n',d')` represents the
next state. No nonzero, sign, or coprimality hypothesis is required. Expanding the gap gives

```text
d'−n'=μ(HAd−3(Pd−Vn)).                                 (2)
```

Every raw successor gap therefore contains `μ`. Gcd normalization is the only place where this
factor can be lost.

## One Deletion

Write `β=k+1` and `3^k=2t+1`; then `ρ=6t+3`. Begin at the distinguished reset `q=1` and apply
the literal singleton block `D_c`. Its normalized carrier is

```text
n₁=(2t+1)(15t+7),
d₁=(6t+1)(5t+2).                                       (3)
```

The formal proof supplies an explicit Bézout certificate for `IsCoprime n₁ d₁`, proves that
this pair represents the actual centered state, and computes

```text
n₁−d₁=μ>ρ.                                              (4)
```

For `β=3`, this is `q=603/550` with primitive gap `53>27`. The proposed universal inequality
`|d−n|<ρ` is false after one physical block.

## Two Deletions

Apply literal `D_c` again. Cancelling the exact common factor in (1) gives

```text
n₂=180t³+192t²+87t+16,
d₂=(6t+1)(30t²+15t+1).                                 (5)
```

Lean again supplies an explicit Bézout certificate, transports the reduced pair through the
centered recurrence, and proves

```text
n₂−d₂=ρμ.                                               (6)
```

For `β=3`, this is `q=14956/13525` with primitive gap `1431=27·53`. A nonzero primitive gap can
therefore acquire the entire `ρ` modulus after two physical blocks. The replacement invariant
`ρ∤d−n` is also false.

## Boundary

Neither carrier in (3) or (5) is asserted to be a pole. The counterexamples do not refute an
inequality or congruence conditioned on a prospective target's Neary language, nor do they
exclude an earliest-pole invariant. They prove that carrier reachability alone cannot consume
the divisibility theorem of `MM-S59`. The next attack must track target suffix ancestry jointly
with gcd cancellation in (1), or prove that the `ρ`-divisible carrier states cannot be the first
physical threshold hit. No `M₅(3)` conclusion follows.

## Verification

[`SwappedSetterCarrierGap.lean`](../MatrixMortality/SwappedSetterCarrierGap.lean) contains the
integral carrier lift, raw gap factorization, explicit primitive coordinates for one and two
distinguished `D_c` steps, coprimality certificates, centered-state representation theorems, and
the exact gap formulas. The module builds warning-free, its namespace passes all default
environment linters, and its publication-facing declarations are listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterCarrierGap.lean`](../MatrixMortality/SwappedSetterCarrierGap.lean)
- [`MM-S59`](../SALVAGE.md#mm-s59-multiplicative-threshold-suffix-carry)
- [`MM-S61`](../SALVAGE.md#mm-s61-primitive-carrier-gap-no-go)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
