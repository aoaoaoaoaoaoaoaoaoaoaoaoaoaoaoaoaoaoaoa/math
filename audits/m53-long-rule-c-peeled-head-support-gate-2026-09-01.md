# Long `R_c` Peeled-Head Support-Gate Audit

**Date:** 2026-09-01
**Target:** factorwise primitive-gap support on the full long `cb/cc` singleton branch
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** every pole obeys one head-support product; `cb` is exactly saturated, while `cc`
exposes the explicit fringe residue `18F−35`

## Pole Reduction

Let `H` be the peeled-head code and `k` the intervening upper length. Exact suffix exhaustion
gives `δ=H·10^(k−1)`, while the upper scale is `10^k`. Cancelling the common power of ten from
the singleton-pole equation leaves

```text
H(TS−7EμGA)=10GVμS.                                  (1)
```

Write the current trace as `T=EP+GV` and the full gap as `E=9q`. Reducing (1) modulo `q`, then
cancelling the lift and singleton trace, which are both units modulo `q`, yields

```text
q∣V(H−10μ).                                          (2)
```

Lean verifies the rational-to-integral passage explicitly; no denominator or projective scale
is discarded silently.

## Head Split

For the terminal `cb` peeled head, its code is `μ+50·10^β`. The marker relation
`9μ=52·10^β−7` gives

```text
H−10μ=−(2·10^β−7)=−q.                               (3)
```

Thus (2) carries no current-code information on the `cb` chamber.

For the `cc` head, let `F` be the code of the remaining `β` fringe digits. Direct code and marker
calculation gives

```text
18(H−10μ)=18F−25q−35.                                (4)
```

Multiplying (2) by eighteen and using (4) proves

```text
q∣V(18F−35).                                         (5)
```

For any divisor `r∣q`, coprimality of `r` with the fringe residue in (5) forces `r∣V`.

## Scope

The support theorem is conditional on a long `R_c` singleton pole with lawful multi-role
current and intervening blocks at `β≥3`. The two head identities are unconditional. The audit
does not claim that every `cc` fringe residue is coprime to `q`, nor that the support-saturated
`cb` chamber is reachable.

## Verification

The dedicated module and root aggregate build without warnings. Selected namespace lint, full
axiom audit, forbidden-aperture scan, and whitespace checks pass. Every selected theorem depends
only on the reviewed standard axiom set.

## Artifacts

- [`DecimalSetterThreeBlockLongSupport.lean`](../MatrixMortality/DecimalSetterThreeBlockLongSupport.lean)
- [`DecimalSetterThreeBlockLongContamination.lean`](../MatrixMortality/DecimalSetterThreeBlockLongContamination.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s101-long-r_c-peeled-head-support-gate)
