# M₄(3) phase-zero right-`c` bounded `x=211` extinction audit

**Date:** 31 August 2026

**Status:** the explicit bounded `cb` valuation-density chamber is formally extinct

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** compose the physical SFFT and density reductions with the terminal grammar gaps

## Verdict

Let a physical body in the outer-wait-`211` `cb` chamber have both decompositions

```text
tail = c^j b rest = stem b c^h.
```

If `h≤5`, `j≤13`, and `z<3^13`, its primitive phase-zero right-`c` core is nonzero for every
middle wait `y`. No parity hypothesis is required by this local theorem.

## Proof Boundary

The proof has four independently checked layers.

1. The physical SFFT product and the exact trailing complement factorization force truncated
   3-adic orders `u,v` with `h+3≤u`, `u+v=h+16`, and `v≤13`. Exact-order transport through
   3-adic units identifies the two wait shells. This derivation assumes only `h≤5` and
   `z<3^13` beyond the core equation and last-`b` decomposition.
2. The physical core equation gives an exact balance between suffix scale and complement.
   First- and last-`b` density bounds convert it into two cleared integer inequalities. These
   inequalities force `22529≤y`; the global theorem `M4-S32` forces `y≤51767`.
3. Under `j≤13`, the exact finite certificate reduces the valuation and density envelopes to
   ten triples `(h,y,z)` and proves `j=0` in every survivor.
4. Substitution of each triple into the exact suffix core forces one of two strict complement
   intervals. Both intervals are forbidden by the generic first-`b` position gap `M4-S35`.

The repository generator emits the finite Lean certificate deterministically. The generated
proofs recheck every numerical branch with `norm_num` and `omega`; `--check` rejects stale
output. No proof depends on the generator at runtime or on a temporary artifact.

## Scope

The final theorem exposes all three numerical restrictions: `h≤5`, `j≤13`, and `z<3^13`.
None is promoted from bounded computation into a global theorem. The result therefore does not
close the full `cb` chamber and does not settle `M₄(3)`.

The middle wait has no assumed search cap. Its lower and upper bounds are formal consequences
of the physical zero. The density envelope alone cannot bound `z`: Lean proves that it holds for
every `z≥394` at `h=j=0` and `y=39726`, so that escape direction needs valuation or grammar
information.

## Validation

The generated-source freshness checks, umbrella build, default namespace linters, Lean LSP
diagnostics, and axiom-snapshot comparison pass under Lean `4.33.1`. Every publication-facing
theorem draws only from `propext`, `Classical.choice`, and `Quot.sound`. No
`sorry`, project axiom, unsafe declaration, proof aperture, external declaration, or linter
suppression was added.

## Artifacts

[`MatrixMortality/ParabolicFirstBOneValuation.lean`](../MatrixMortality/ParabolicFirstBOneValuation.lean),
[`MatrixMortality/ParabolicFirstBOneFunnel.lean`](../MatrixMortality/ParabolicFirstBOneFunnel.lean),
[`MatrixMortality/ParabolicFirstBOneClosure.lean`](../MatrixMortality/ParabolicFirstBOneClosure.lean),
[`MatrixMortality/ParabolicFirstBOnePhysical.lean`](../MatrixMortality/ParabolicFirstBOnePhysical.lean),
and
[`scripts/generate-parabolic-first-b-one-funnel.py`](../scripts/generate-parabolic-first-b-one-funnel.py)
