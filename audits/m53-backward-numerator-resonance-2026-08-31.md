# Backward Numerator Resonance Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the deep numerator cylinder behind a final literal deletion pulls backward through
one physical block, and another literal deletion toggles it exactly into the full carrier-gap
cylinder

[`MM-S64`](../SALVAGE.md#mm-s64-unique-predecessor-cylinder) shows that a nonterminal
full-erasure-tail pole after literal `D_c` forces `3^(β−1)` into the preceding primitive
numerator. This audit computes the exact inverse constraint on the block before that carrier.

## Numerator Pullback

Let primitive `(m,e)` cross a physical role block `w` to primitive `(n,d)`. Write the raw
successor as `t(n,d)` and put

```text
a=upperLength(w),      E=P_we−V_wm,      g=v₃(t).
```

Assume `n≠0` and

```text
3^(β−1) ∣ n.                                            (1)
```

Primitivity makes `d` a three-adic unit. The denominator `e` before the block is also a unit.
Indeed, if `3∣e`, then primitivity makes `m` a unit; the physical lower code makes `E` a unit;
the denominator normalization makes `t` a unit; and the raw numerator is a unit. This
contradicts (1).

The exact normalization equations are

```text
t d=R E,
t n=H(E−μ3^a e).                                       (2)
```

The first equation gives `v₃(E)=g`. In the second, the two terms inside parentheses have depths
`g` and `a`. Its left side has depth at least `g+β−1`. Unequal depths cannot survive that far,
so

```text
g=a.                                                    (3)
```

Multiplying the divisibilities in (1) and (3), then cancelling the unit `H`, gives the complete
predecessor cylinder

```text
3^(a+β−1) ∣ E−μ3^a e.                                  (4)
```

## Literal Toggle

For `w=D_c`, `a=1`, `P_w=H`, and `V_w=2`. The expression in (4) is

```text
He−2m−3μe=2(e−m)−3^βe.
```

After cancelling the factor two, (4) is exactly

```text
3^β ∣ e−m.                                             (5)
```

Thus backward traversal through literal `D_c` sends the deep-numerator state to the full-gap
state. Together with `MM-S64`, which sends a full-gap successor backward through literal `D_c`
to a deep predecessor numerator, this is a two-state ancestry toggle.

## Zero Fork

The assumption `n≠0` in the valuation comparison does not leave an open physical case. A
represented carrier `(0,d)` with `d≠0` lies on the ordinary ray. Its literal-`D_c` successor is
represented by `(1,1)`. Every physical pole from that state therefore satisfies `P=V`; the
checked Neary decoder proves `TagHaltsFrom`.

Lean composes the branches without a side assumption: after two final literal `D_c` blocks, a
nonterminal full-erasure-tail pole either proves the source halt or forces (5) on the carrier
before the pair.

## Boundary

The result does not yet classify a first non-literal-`D_c` predecessor satisfying (4). Nor does
it prove that a zero full gap is the exact raw-head constructor consumed by the local
first-multi extinction theorem, although it is projectively the distinguished ratio. Finally,
the physical composition still assumes that the target ends in `β` erasure tiles; generic role
blocks need only end in one.

## Verification

[`SwappedSetterBackwardResonance.lean`](../MatrixMortality/SwappedSetterBackwardResonance.lean)
contains the unit forcing, exact resonance, predecessor cylinder, literal toggle, zero-carrier
terminal theorem, and two-block physical composition. The module builds warning-free; its
namespace passes all default environment linters; LSP reports no diagnostics; and every public
declaration is listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterBackwardResonance.lean`](../MatrixMortality/SwappedSetterBackwardResonance.lean)
- [`MM-S64`](../SALVAGE.md#mm-s64-unique-predecessor-cylinder)
- [`MM-S68`](../SALVAGE.md#mm-s68-backward-numerator-resonance)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
