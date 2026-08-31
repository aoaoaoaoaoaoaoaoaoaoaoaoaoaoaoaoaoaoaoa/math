# Double-Deletion Ratio-Chamber Extinction Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the expected-shell swapped-ternary first multi-transfer interface is empty

This audit consumes the literal `D_c²→multi` branch left by
[`MM-S50`](../SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction). It does not assume the
integral discrepancy or common-suffix witness required by the raw-fringe classifier.

## Transfer Chamber

Put `ρ=3^β`, `μ=2ρ−1`, `H=5ρ−1`, and `D=ρ−2`. For the punctuated upper carrier preceding
the literal middle block `D_c²`, let

```text
q=(μA−P)/P.
```

The exact middle codes are `P_m=14ρ−1`, `V_m=8`, and the normalized discrepancy is

```text
Δ=(14ρ−1)/3 − 8Hq/(3D).                                (1)
```

The complete punctuated upper cylinder gives

```text
−1/(2ρ)<q<1.                                            (2)
```

For `β≥6`, substitution of (2) into (1), followed by exact denominator clearing, proves

```text
6Hμ/(3D+2H) < Δ < 9Hμ/(4D+3H).                         (3)
```

The two residual polynomial inequalities are certified after shifting `ρ` by `729=3^6`; all
coefficients and constant terms are positive.

## Target Ratio

A following physical pole has the normalized equation

```text
ΔDP_t=H(3μ−Δ)V_t.                                      (4)
```

The target codes are positive, and the general pole interval gives `0<Δ<3μ`. Therefore every
factor used to cross-multiply (3) and (4) is positive. The lower and upper bounds in (3) become

```text
2/3 < V_t/P_t < 3/4.                                   (5)
```

`doubleDeletion_pole_targetRatio` formalizes this implication without assuming a target depth,
target upper length, or integral carrier discrepancy.

## Physical Gap

Let `N` be the length of the swapped punctuated upper word and `M` the length of the swapped
lower word. Nonzero ternary coding gives

```text
3^(n−1) ≤ code(word) < 3^n.                             (6)
```

The two strict inequalities in (5) imply `2P_t<3V_t` and `4V_t<3P_t`. Combining these with
(6) forces exactly `M=N` or `M+1=N`.

For `M=N`, the first physical role excludes (5):

- an erasure begins with lower digit `2` and upper digit `1`;
- `R_b` has lower prefix `112` and upper prefix `122`;
- `R_c` has lower prefix `112` because the compiler body begins in `b`, while its upper word
  has prefix `11`.

Each case gives `3P_t<4V_t`. For `M+1=N`, every head other than `D_c` gives
`3V_t<2P_t` from the upper prefix `12` or the `11/112` comparison. A leading `D_c` contributes
upper digit `1` and lower digit `2`; these terms cancel exactly in `2P_t−3V_t`, so induction
strips the role. The final-erasure base cannot have adjacent lengths because the upper marker
remains. Thus no physical role block occupies (5).

## Composed Boundary

`doubleDeletion_avoids_role_pole` combines the transfer chamber and physical gap.
`firstMultiTransfer_pole_false` then consumes
`firstMultiTransfer_pole_forces_doubleDeletion` from `MM-S50`. Under the compiler body envelope,
expected coefficient shells and lower-code units, and the centered first-transfer hypotheses of
`MM-S35`, no first multi-transfer pole exists. The later
[`MM-S55`](../SALVAGE.md#mm-s55-physical-role-block-shell-completion) theorem proves that every
physical role block supplies those shells and lower units automatically.

This closes that interface, not projective avoidance. The remaining master obligation is the
global earliest-pole reduction: prove every arbitrary swapped product not already killed by the
distinguished-boundary theorems enters this interface, or classify the missing initial/shell
constructor.

## Verification

[`SwappedSetterDoubleDeletion.lean`](../MatrixMortality/SwappedSetterDoubleDeletion.lean) proves
equations (1)-(5), the complete physical ratio gap, and the composed extinction theorem. The
module builds warning-free and contains no proof aperture. An independent reconstruction of the
ratio-gap argument reached the same length dichotomy and prefix cases. Publication-facing
declarations are listed in `AxiomAudit.lean` and compared against the canonical axiom snapshot.

## Artifacts

- [`SwappedSetterDoubleDeletion.lean`](../MatrixMortality/SwappedSetterDoubleDeletion.lean)
- [`MM-S35`](../SALVAGE.md#mm-s35-first-multi-transfer-trichotomy)
- [`MM-S50`](../SALVAGE.md#mm-s50-long-all-erasure-singleton-extinction)
- [`MM-S51`](../SALVAGE.md#mm-s51-double-deletion-ratio-chamber-extinction)
- [`FRONTIER.md`](../FRONTIER.md)
- [`FORMALIZATION.md`](../FORMALIZATION.md)
