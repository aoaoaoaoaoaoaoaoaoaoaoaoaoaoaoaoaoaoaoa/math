# Decimal Setter Length-Two Chamber Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** both ordinary-reset A-to-A length-two resonances miss every admissible next pole

This audit closes the A-to-A survivor isolated by
[`MM-S13`](../SALVAGE.md#mm-s13-decimal-one-transfer-extinction) and
[`MM-S14`](../SALVAGE.md#mm-s14-ordinary-depth-two-shell-forest). It does not prove
arbitrary-depth projective avoidance or settle `M₅(3)`.

## J-Fraction Coordinate

Put `ρ=10^β`, where compiler-emitted widths satisfy `β≥3`, and write

```text
u=P/(μA),             v=LV/(μA),
F(u,v,t)=u+v−v/t,     q(u,v)=v/(u+v).
```

The current projective state is `t`; the next block is singular exactly when
`t=q(u,v)`. Every positive admissible coefficient pair has `0<q(u,v)<1`.

For every encoded upper spelling beginning in digit `5`, Lean proves the uniform window

```text
4/5 < u < 101/100.                                  (1)
```

The lower spelling begins either in digit `7` or in digits `55`. Comparing its length with
the upper length plus `β` yields the disjoint bounds

```text
low shell:   v<4,       q<9/10;
high shell:  v>53/2,    q>963/1000.                 (2)
```

The declarations `encodedJUpper_in_window`, `lowShell_pole_below`, and
`highShell_pole_above` check (1) and (2) over `ℚ`.

## Two Deletions

The all-erasure length-two block `D_cD_c` has upper and lower spellings `55` and `77`.
Exact rational inequalities give, for every source state satisfying (1),

```text
961/1000 < F_DcDc(t) < 963/1000.                    (3)
```

Equation (2) places every admissible target pole strictly outside (3). This excludes both
possible target-prefix classes without an asymptotic estimate or numerical oracle.
`doubleDeletion_step_in_gap`, `doubleDeletion_avoids_falsePrefixPole`, and
`doubleDeletion_avoids_trueTruePrefixPole` are the consuming Lean theorems.

## Rule Then Deletion

The other length-two phase word is `R_cD_c`. Its lower spelling includes the encoded Neary body.
The compiler grammar proves that the body begins in `b` and has enough length to force the lower
spelling to begin `55` with total length at least `2β+4`. Consequently

```text
normalized lower ≥55ρ²,       v>265ρ.               (4)
```

There are two possible source prefixes. A source beginning in `c` has `t<97/100`; (4) makes
`F_RcDc(t)<0`. A source beginning in `b` has `t>1+1/(2μ)`; (4) makes
`F_RcDc(t)>1`. Every positive target pole lies in `(0,1)`, so neither image can be a pole.

The arithmetic conclusions are `ruleDeletion_cLeading_avoids_positivePole` and
`ruleDeletion_bLeading_avoids_positivePole`. `compiler_body_head_b` and
`compiler_ruleDeletionLowerWord_shape` derive the required prefix and length directly from
`NearyCompiler.body`; they are not assumptions supplied by the chamber theorem.

## Consequence And Boundary

An admissible all-`c` block ends in deletion, so its two roles are exactly `D_cD_c` or
`R_cD_c`. The two cases above exhaust the middle-length-two A-to-A resonance. Combined with
the shell gate, every ordinary-reset depth-two A-to-A false pole either enters the already
peeled one-digit distinguished reset or is impossible. Thus the ordinary A-to-A branch is
closed.

The result does not decide the ordinary A-to-B and B-to-A resonances, the distinguished-reset
depth-two branch, or any deeper normalized-suffix orbit. The distinguished branch remains the
unbounded part of the decimal setter frontier.

## Verification

The module build, namespace lint, Lean language-server diagnostics, and selected transitive
axiom snapshots pass without warnings, suppressions, or proof apertures. The publication-facing
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, matching
`verification/axioms.txt`.

## Artifacts

- [`DecimalSetterChamber.lean`](../MatrixMortality/DecimalSetterChamber.lean)
- [`DecimalSetterCarry.lean`](../MatrixMortality/DecimalSetterCarry.lean)
- [`SALVAGE.md`](../SALVAGE.md#mm-s15-ordinary-a-to-a-length-two-extinction)
