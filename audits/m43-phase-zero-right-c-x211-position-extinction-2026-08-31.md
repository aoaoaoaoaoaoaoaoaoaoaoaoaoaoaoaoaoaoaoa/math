# M₄(3) phase-zero right-`c` `x=211` position-extinction audit

**Date:** 31 August 2026

**Status:** the late next-`b` exit from M4-S36 is formally extinct

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** derive the finite next-`b` position bound rather than assume it

## Verdict

Let a physical body in the outer-wait-`211` `cb` chamber have both decompositions

```text
tail = c^j b rest = stem b c^h.
```

If `h≤5` and `z<3^13`, its primitive phase-zero right-`c` core is nonzero for every `j` and
middle wait `y`. The position restriction in M4-S36 is therefore discharged.

## Proof Boundary

The proof has four checked layers.

1. M4-S36 supplies the physical valuation and density envelopes and derives
   `22529≤y≤51767` from a hypothetical zero.
2. Under `j≥13`, exact cancellation of the position power contracts the density inequalities
   to `0<A−39J` and `242·3^13·(A−39J)≤B+39J`. These contain neither `h` nor `j`.
3. Writing `k=y−22529`, the strip first forces `k≤817`. Exact classification of that common
   parameter leaves eleven values of `y`. For every `h≤5`, each contradicts the base
   divisibility `3^(h+3) ∣ y−r_h` in the valuation envelope. Hence `j<13`.
4. The derived bound enters the existing S36 certificate, which reduces to ten triples and
   extinguishes their two terminal grammar gaps.

The finite reflection is a kernel proof over `k=0,…,817`, after an analytic reduction from the
original unbounded variables. It does not enumerate words, positions, trailing runs, or raw
multi-parameter boxes. No temporary artifact or external checker is trusted.

## Scope

The final theorem retains `h≤5` and `z<3^13`. It removes only the next-`b` position hypothesis;
the exits `h≥6` and `z≥3^13` remain open. No parity hypothesis is used.

## Validation

The umbrella build, default namespace linters, Lean LSP diagnostics, and axiom-snapshot
comparison pass under Lean `4.33.1`. Every publication-facing theorem draws only from
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, project axiom, unsafe declaration,
proof aperture, external declaration, or linter suppression was added.

## Artifacts

[`MatrixMortality/ParabolicFirstBOnePosition.lean`](../MatrixMortality/ParabolicFirstBOnePosition.lean),
[`MatrixMortality/ParabolicFirstBOnePhysical.lean`](../MatrixMortality/ParabolicFirstBOnePhysical.lean),
and
[`audits/m43-phase-zero-right-c-bounded-x211-extinction-2026-08-31.md`](m43-phase-zero-right-c-bounded-x211-extinction-2026-08-31.md)
