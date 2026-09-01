# Reachable Predecessor-Cylinder Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the non-`D_c` predecessor cylinder isolated by `MM-S71` is physically reachable, so
no block-local grammar or residue argument can empty it

## Witness

Set `β=3`, choose compiler body `bbcc`, and let `B=[R_c,D_c]`. Starting from the ordinary
reset, the history `B²` reaches the primitive represented defect ratio

```text
m/e = −570661367816 / 106465174525.
```

Both integers are coprime. Applying `B` once more gives raw coordinates equal to `−3` times the
primitive pair

```text
n = −607561904608405895896,
d =  113351524805114612975.
```

These are also coprime, and

```text
d−n = 27·26700497385685944773 ≠ 0.
```

## Cylinder

The block has upper length two. At width three its punctuated upper and lower codes and terminal
discrepancy are

```text
P_B=377,      V_B=23835752,      H=134.
```

The discarded scale has exact three-adic depth one, and direct evaluation gives

```text
P_Be−V_Bm−3He = 27·503782969541244241.
```

This is exactly the `a=2`, `g=1`, `β=3` predecessor cylinder from `MM-S71`.

## Boundary

The witness is not a target pole and does not refute the setter construction. It shows that the
cylinder is an exact reachable preimage condition rather than a contradiction. Any surviving
proof must preserve information discarded by the carrier-gap projection: the target's balanced
suffix carry, a first-pole condition, or stronger exact history ancestry.

## Verification

[`SwappedSetterReachableCylinder.lean`](../MatrixMortality/SwappedSetterReachableCylinder.lean)
kernel-checks the represented history, both gcd normalizations, the raw recurrence, the nonzero
full-modulus successor gap, and the cylinder divisibility. The module builds warning-free; its
namespace passes all default linters; LSP reports no diagnostics; and its public theorem is
listed in `AxiomAudit.lean`.

## Artifacts

- [`SwappedSetterReachableCylinder.lean`](../MatrixMortality/SwappedSetterReachableCylinder.lean)
- [`MM-S71`](../SALVAGE.md#mm-s71-three-block-backward-frontier)
- [`MM-O27`](../SALVAGE.md#mm-o27-reachable-predecessor-cylinder)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
