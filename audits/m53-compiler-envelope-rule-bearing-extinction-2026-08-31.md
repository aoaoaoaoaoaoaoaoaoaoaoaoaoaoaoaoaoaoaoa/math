# Compiler-Envelope Rule-Bearing Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every rule-bearing phase of the two live swapped-ternary first multi-transfer
shapes is impossible under the compiler body envelope

This audit composes the three-shape gate [`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy)
with the singleton-`D_b` extinction [`MM-S38`](../SALVAGE.md#mm-s38-two-c-singleton-b-extinction).
It addresses the first multi-transfer pole only.

## Initial Cylinder

Put `ρ=3^β`, `μ=2ρ−1`, and `H=5ρ−1`. For the first block let `A=3^m` be its upper power and
let `P` be its punctuated swapped upper code. Define

```text
q=(μA−P)/P.                                               (1)
```

Induction over the complete role word gives the cylinder

```text
ρA ≤ P < 2ρA.                                             (2)
```

The first role refines (2). Its exact upper recurrence yields

```text
first letter c:   q>(ρ−3)/(5ρ),
first letter b:   q<−2/(9ρ).                              (3)
```

These inequalities retain every later role and phase; no bounded-fringe assumption is used.

## Compiler Lower Bound

The Neary compiler body satisfies

```text
|body|≥β−1,       head(body)=b.
```

Consequently its binary tag encoding has length at least `2β`. The lower spelling of `R_c`
contains that encoding and has length at least `2β+3`; every other role image is nonempty.
If an all-`c` middle block has role length `n` and contains `R_c`, its swapped lower code obeys

```text
V_m ≥ 3^(n+2β+1)=9ρ²·3^(n−1).                            (4)
```

The upper cylinder simultaneously gives

```text
P_m < 6ρ·3^(n−1).                                        (5)
```

The head-`b` hypothesis is essential. The theorem makes no assertion for arbitrary bodies.

## Pole Interval

Let `T=3^(n−1)`. Factoring the centered recurrence after the middle transfer produces

```text
Δ=P_m/T − H V_m q/((ρ−2)T).                              (6)
```

For any nonempty physical target block with upper and lower codes `P_t,V_t>0`, its coefficient
is `−((ρ−2)P_t+HV_t)`. The next pole equation is therefore

```text
−((ρ−2)P_t+HV_t)Δ+3HμV_t=0,
```

which forces

```text
0<Δ<3μ.                                                   (7)
```

If the first block begins in `c`, equations (3)--(5) imply
`HV_mq>(ρ−2)P_m`, hence `Δ≤0`. If it begins in `b`, they imply
`−HV_mq>3μ(ρ−2)T`, hence `Δ>3μ`. Both alternatives contradict (7).

## Exact Survivor Set

Every all-`c` block containing no `R_c` is literally an all-`D_c` block. Applying the preceding
cut to the two live `MM-S35` shapes, then applying `MM-S38` to its third shape, leaves exactly

```text
D_c²          before a depth-one target,
D_c^(β+1)     before a depth-β target.                    (8)
```

Equation (8) is necessary, not existential. The proof does not establish reachability of either
block and does not classify later product residuals.

## Verification

[`SwappedSetterCylinder.lean`](../MatrixMortality/SwappedSetterCylinder.lean) proves the complete
upper cylinder, the compiler lower-code bound, the normalized pole interval, both leading-letter
contradictions, and the packaged survivor theorem. The module is warning-free, passes the default
environment linter, and contains no proof aperture. `AxiomAudit.lean` lists both public theorems;
the canonical snapshot is regenerated after concurrent integration.

## Artifacts

- [`SwappedSetterCylinder.lean`](../MatrixMortality/SwappedSetterCylinder.lean)
- [`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy)
- [`MM-S38`](../SALVAGE.md#mm-s38-two-c-singleton-b-extinction)
- [`MM-S44`](../SALVAGE.md#mm-s44-compiler-envelope-rule-bearing-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
