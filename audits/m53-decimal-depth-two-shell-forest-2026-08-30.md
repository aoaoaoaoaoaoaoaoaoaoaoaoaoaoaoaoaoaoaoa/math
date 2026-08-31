# Decimal Setter Depth-Two Shell Forest Audit

**Date:** 2026-08-30
**Target:** three `5 × 5` integer matrices
**Authors:** GPT-5.6 Sol; elicited by @eternalism_4eva
**Verdict:** the ordinary-reset depth-two search collapses to three explicit resonant families;
the singleton-to-singleton branch is empty

This audit extends the one-transfer extinction theorem. It is a valuation gate, not a proof of
arbitrary-depth projective avoidance or of `M₅(3)` undecidability.

## Backward Trace

Retain the exact depth-two identity extending
[`MM-S13`](../SALVAGE.md#mm-s13-decimal-first-transfer-extinction):

```text
K₂R₁=μGV₂10^(m₁)T₃,
K₂=T₂T₃−EμG10^(m₂)V₃.                         (1)
```

At the ordinary reset, `R₁=P₁` is a decimal unit. All coefficients in (1) other than the
traces and powers of ten are units. Write

```text
A=(1,1),             B=(β+1,β)
```

for the joint `(2,5)` shells of a multi-role and singleton-erasure trace. If `T₂` has shell
`(a₂,b₂)` and `T₃` has shell `(a₃,b₃)`, the two summands in `K₂` have shells

```text
(a₂+a₃,b₂+b₃),       (m₂,m₂).                    (2)
```

Whenever the entries differ at a prime, the smaller valuation survives subtraction. The right
side of (1) has shell

```text
(m₁+a₃,m₁+b₃).                                           (3)
```

Lean proves (1), the coordinatewise nonresonant subtraction, and (3) as
`twoTransferTrace_identity`, `twoTransferTrace_shell_of_nonresonant`, and
`ordinaryTwo_shellBalance`.

## Complete Ordinary Shell Table

The four possibilities for `(T₂,T₃)` are as follows.

| Middle / target | Backward-trace comparison | Exact survivor |
| --- | --- | --- |
| A / A | `(2,2)` versus `(m₂,m₂)` | `m₂=2`, or `m₁=1` and entry into the peeled distinguished reset |
| A / B | `(β+2,β+1)` versus `(m₂,m₂)` | `m₂∈{β+1,β+2}`, or `m₁=1` |
| B / A | `(β+2,β+1)` versus the singleton middle length | middle `D_b` and `m₁=β` |
| B / B | `(2β+2,2β)` versus the singleton middle length | none |

For A/B, away from `m₂=β+1,β+2`, both coordinates are nonresonant. If `m₂≤β`,
the backward trace has equal coordinates, contradicting the unit gap in (3). If `m₂≥β+3`,
its shell is `(β+2,β+1)`, and (3) forces `m₁=1`.

For B/A, the middle singleton is either `D_c`, of upper length one, or `D_b`, of upper length
`β+2`. The `D_c` backward trace has shell `(1,1)`, which would force the nonempty first block
to have length zero. At `D_b`, the `2`-coordinate resonates, but the `5`-coordinate remains
exactly `β+1`; comparison with (3) forces `m₁=β`.

For B/B, `D_c` again leaves shell `(1,1)`. At `D_b`, the scale `(β+2,β+2)` lies strictly
below both product coordinates for `β≥3`, so it survives intact. In either case the backward
trace has equal coordinates, while (3) has gap one. The branch is impossible.

The specialized Lean declarations are `ordinaryTwoMulti_gate`,
`ordinaryTwoMultiToSingleton_gate`, `ordinaryTwoSingletonToMulti_gate`, and
`ordinaryTwoSingletonToSingleton_impossible`.

## Grammar Consequences

A multi-role upper spelling of total length `β+1` or `β+2` cannot contain `b`: one `b` role
already costs `β+2` digits and a multi-role block contains another positive-length role. Thus
the two A/B resonances are all-`c` middle blocks. In the B/A survivor, the first block has upper
length `β` and is likewise all `c`, followed by the singleton `D_b` middle block.

After the one-digit reductions are removed, the complete ordinary depth-two shell frontier is
therefore:

```text
A → A:  two c roles;
A → B:  β+1 or β+2 c roles;
B → A:  β c roles, then D_b;
B → B:  impossible.
```

Nonfinal all-`c` roles may still be rule or erasure phase; admissibility fixes the final role to
erasure. The shell theorem does not decide those phase words.

## Scope And Next Cut

This is a complete shell classification only for a depth-two pole orbit starting at the
ordinary reset. It does not classify the distinguished-reset discrepancy `R₁=P₁−V₁`, where
the normalized common suffix remains live. Nor does it kill the three resonant ordinary
families; they require Archimedean pole intervals or normalized decimal suffixes.

Every exact search should now delete all other ordinary depth-two words before enumeration.
The immediate targets are the two-role A/A family, the two long all-`c` A/B families, and the
`β`-`c`/`D_b` B/A family.

## Verification

The module build, namespace lint, Lean language-server diagnostics, and selected transitive
axiom snapshots pass without warnings, suppressions, or proof apertures.

## Artifacts

- [`DecimalSetterCarry.lean`](../MatrixMortality/DecimalSetterCarry.lean)
- [`m53-decimal-setter-one-transfer-2026-08-30.md`](m53-decimal-setter-one-transfer-2026-08-30.md)
- [`SALVAGE.md`](../SALVAGE.md#mm-s14-ordinary-depth-two-shell-forest)
