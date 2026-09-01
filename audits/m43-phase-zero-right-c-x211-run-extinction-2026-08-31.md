# M₄(3) phase-zero right-`c` `x=211` run-extinction audit

**Date:** 31 August 2026

**Status:** the long trailing-`c` exit from M4-S36 is formally extinct

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** derive the trailing-run bound rather than assume it

## Verdict

Let a physical body in the outer-wait-`211` `cb` chamber have both decompositions

```text
tail = c^j b rest = stem b c^h.
```

If `z<3^13`, its primitive phase-zero right-`c` core is nonzero for every `h`, `j`, and
middle wait `y`. The trailing-run and next-`b` restrictions in M4-S36 are both discharged.

## Proof Boundary

The final-`b` decomposition gives exact integral scale and complement coordinates. For
`h≥6`, the SFFT product gives `v₃(U)+v₃(V)=h+16`. The universal `V` root modulo `3^13` and
the retained inner-wait bound force `v₃(V)≤13`, hence `v₃(U)≥h+3`.

Exact `U` congruences leave two waits at `h=6`, one at `h=7`, and one at `h=8`. Density
eliminates the first three. The `h=8` chamber forces `(j,z)=(0,1)` and exact orders
`v₃(U)=11`, `v₃(V)=2`, contradicting their required sum. Runs `h≥9` force middle-wait
residues outside `22529≤y≤51767`.

The physical composition first proves `y≥2` directly from the exact complement balance; it
then derives density and the global middle-wait interval. If `h≤5`, M4-S37 and M4-S36 apply.
If `h≥6`, the run-coordinate theorem gives the contradiction above. No finite word census,
experimental cap, or temporary artifact enters the proof.

## Scope

The final theorem retains exactly `z<3^13`. It assumes both displayed decompositions, which
are the physical grammar interface for a body containing `b`. It does not exclude the
large-inner-wait cylinder `z≥3^13` and therefore does not yet close the complete `cb` chamber.

## Validation

The umbrella build, default namespace linters, Lean LSP diagnostics, and axiom-snapshot
comparison pass under Lean `4.33.1`. Every publication-facing theorem draws only from
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, project axiom, unsafe declaration,
proof aperture, external declaration, or linter suppression was added.

## Artifacts

[`MatrixMortality/ParabolicFirstBOneRun.lean`](../MatrixMortality/ParabolicFirstBOneRun.lean),
[`MatrixMortality/ParabolicFirstBOnePhysical.lean`](../MatrixMortality/ParabolicFirstBOnePhysical.lean),
and
[`MatrixMortality/ParabolicFirstBOneValuation.lean`](../MatrixMortality/ParabolicFirstBOneValuation.lean)
