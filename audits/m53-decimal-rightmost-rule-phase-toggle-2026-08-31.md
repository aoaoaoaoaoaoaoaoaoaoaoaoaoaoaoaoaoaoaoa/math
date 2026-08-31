# Decimal Rightmost-Rule Phase-Toggle Audit

**Date:** 2026-08-31
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the remaining rule-bearing raw-entry grammar has three exact rightmost-rule depth
profiles, and every leading `R_cD_c⁺` first block is impossible

## Exact Factorization

Write a rule-bearing word as `u R_x D(t)`, where the suffix `D(t)` consists only of erasures and
has role width `s`. Erasing every phase preserves every tag letter and therefore the complete
upper spelling. On the lower side, removal of the common suffix gives

```text
V(u R_x D(t))−V(D(u) D_x D(t))=10^s K.
```

Every rule lower word ends in decimal digits `557`. The erased companion ends in `7`, `77`, or
`777` according as `|u|` is zero, one, or at least two. Consequently

```text
|u|=0: K≡550 (mod 1000),
|u|=1: K≡480 (mod 1000),
|u|≥2: K≡780 (mod 1000).
```

These are not residue heuristics. Lean derives exact shells `(s+1,s+2)` and `(s+2,s+1)` in
the outer cases. In the middle case it derives exact five-adic depth `s+1` and proves
`2^(s+3)` divides the perturbation.

## Raw Residual

For fixed upper code `P`, the raw residual is

```text
R(V)=H(EP+GV)−10μGV.
```

Direct subtraction gives

```text
R(V₁)−R(V₂)=G(H−10μ)(V₁−V₂).
```

The physical lift `G` is a decimal unit. A lawful two-`c` peeled head ends in digit `7`, so
`H−10μ` is also a decimal unit. The lower-code phase-toggle depths therefore pass unchanged to
the raw residual. Lean also checks both shell transport directions: a deeper perturbation
preserves the companion's target shell, while a perturbation shallower at both primes imposes
its own off-diagonal shell on the companion.

## First Extinction

For `R_cD_c^s` with `s≥1`, the physical multi-role target depth is `s`. Its phase-erased
companion is `D_c^(s+1)`, and the phase perturbation has shell `(s+1,s+2)`, deeper than the
target at both primes. The companion would therefore have the same shell `(s,s)`, contrary to
MM-S53. No member of this infinite leading-rule family survives.

## Boundary

The theorem does not yet exclude a rightmost rule in position two or later, any word containing
a `b` tag, a transition from a generalized carrier, or a singleton target. It replaces that
undifferentiated language by three exact relative-position classes. The next cuts are the
position-two and position-three equality boundaries, followed by the shallow off-diagonal
companion shell for later rules.

## Verification

`MatrixMortality/DecimalSetterPhase.lean` checks upper-spelling invariance, exact lower-code
factorization, all three coefficient congruences, their valuation consequences, calibrated raw
unit factors, shell transport, and the leading-`R_c` extinction. The narrow and root builds,
Lean language-server diagnostics, namespace lint, and selected transitive axiom checks pass
without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterPhase.lean`](../MatrixMortality/DecimalSetterPhase.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s54-rightmost-rule-phase-toggle-trichotomy)
