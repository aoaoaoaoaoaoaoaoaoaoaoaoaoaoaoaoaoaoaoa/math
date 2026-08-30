# M₄(3) safe-wall transport-chamber audit

**Date:** 30 August 2026

**Status:** the safe exterior flag now constrains the transported kernel at the one-sided wall
incidence

**Authorship:** GPT-5.6 Sol; elicited by @eternalism_4eva

**Target:** compose `M4-S04` with the consecutive-wall normal form `M4-S07`

## Verdict

The composition is exact and Lean-checked. Let a nonempty regular safe right wall have exterior
state `(0,v,w)`, let `ξ=(a,b)≠0` be the transported canonical kernel of the left wall, and assume
the consecutive incidence vanishes. The checked cokernel formula gives

```text
(v,-4w)·(a,b)=0,    hence    v a=4 w b.
```

The safe wall's leftmost residue then forces the opposite strict valuation chamber on `ξ`:

```text
right residue 0:  ν₃(w)<ν₃(v)  implies  ν₃(a)<ν₃(b),
right residue 1:  ν₃(v)<ν₃(w)  implies  ν₃(b)<ν₃(a).
```

Here a coordinate on the higher side may be zero; `ValLt` records zero there as infinite
valuation. In particular, a vector with two nonzero coordinates of equal valuation cannot close
against a nonempty safe wall.

## Proof Boundary

`ParabolicBlade.safeWall_incidence_orients_transport` first obtains the wall orientation from
`exteriorState_safe_word_wall_orientation` and rewrites the incidence through
`bridgeCokernel_eq_exteriorTail`. If all four scalar factors are nonzero, applying `padicValRat`
to `v a=4 w b` transfers the strict inequality because `ν₃(4)=0`. If the high wall coordinate
vanishes, the incidence forces the corresponding transported coordinate to vanish; nonzero `ξ`
supplies the other coordinate. The proof treats both phases separately and assumes neither a
chosen outer-product gauge nor a finite valuation bound.

`ParabolicBlade.safeWall_rejects_balanced_transport` is the direct contradiction corollary. Both
theorems quantify over every natural width, nonempty body, regular safe right word, and rational
transport vector.

## Scope

This result does not prove that safe walls exist or are unreachable. It does not constrain a
right wall containing residue-two defects, and it does not yet classify the vectors produced by
arbitrary invertible bridge transport. Its exact contribution is to turn every safe-right-wall
incidence into a strict phase-indexed transport obligation.

The next master cut is therefore the transport action on the only bad defect skeletons left by
`M4-S06`:

```text
m≡1 (mod 4) with opposite safe phases,
m≡3 (mod 4) with equal safe phases.
```

Proving that these transports remain balanced or enter the wrong chamber would exclude the
remaining safe right endpoints. An exact chamber hit would instead supply a concrete candidate
for the one-sided orbit equation.

## Validation

The module target `MatrixMortality.ParabolicIncidence` builds without warnings under Lean
`4.33.1`. No axioms, proof apertures, external declarations, or linter suppressions were added.

## Artifact

[`MatrixMortality/ParabolicIncidence.lean`](../MatrixMortality/ParabolicIncidence.lean)
