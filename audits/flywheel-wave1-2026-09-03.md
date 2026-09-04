# Flywheel wave 1: shared interface barriers in the lower table

Reconciled on 2026-09-04. The [integration audit](reconciliation-2026-09-04.md) records the
completed boundary and rejects the former aggregate six-state claim. The individual reports
are historical evidence; the salvage registry owns the surviving statements.

**Date:** 2026-09-03. **Method:** interface compression (`MM-C06`) decomposes the studied rank
profiles into transition-only and bridge-path problems indexed by their singular generators.
Twelve Sol-xhigh executors attacked those problems in isolated worktrees; each returned a
fixed-shape report. This audit reconciles them. Every claim names the Lean declaration or the
report it rests on.

## The meta-finding

Several undecided cells expose the same low-rank bridge mechanisms. Interface compression makes
that overlap exact at the level of each stated rank profile. It does **not** prove that every open
cell reduces to generic two-generator projective incidence, nor that the open cells are mutually
equivalent. The common projective slice is a hardness cone inside the table, not a collapse of the
whole frontier.

**Specified two-counter architectures.** The attempted valuation-guarded constructions need
independent registers, permanent poison after an illegal read, and compatible control. The
following obstructions have distinct hypotheses; they do not exhaust all small constructions:

- The tested four-mode updater/reader combinations fail to preserve the other register's
  center. A separate exact increment/decrement example has `R_A R_B=4I`, which also repairs
  an illegal decrement (`MM-S107`). Neither example excludes all encodings on `P¹`.
- A prime-integral, unit-determinant Möbius map with an integral finite pole cannot preserve
  the entire negative-valuation chamber (`MM-O31`,
  `TwoPlaceReader.integralFinitePole_breaks_negative`).
- On `P²` the specified mirrored one-cut readers cannot share a nonzero empty return
  (`TwoRegisterPlaneNoGo.no_common_scaled_xReader_yReader_of_xPoleAtOne`).

The two-cut follow-up also failed in its prescribed diagonal realization. Its constant reader
coefficient has a nonzero `2 × 2` minor; together with four distinct nonconstant modes this
requires at least six coordinates (`MM-O33`, `TwoVertexPlaneNoGo`). This mode count does not
classify arbitrary readers. The later `WallEnvelope` wrapper assumed its surviving six-mode
allocation and was removed during reconciliation; it supplied no universal dimension barrier.

**Determinant-valuation descent.** The proposed well-founded descent for the
unary return arteries (`M₄(2)^{(4,2)}`, `M₃(2)^{(3,2)}`), the total determinant valuation, is
refuted by exactly the transverse-reservoir cycle that already blocks `M₃(2)`
(`reports/D.md`; `ReturnGuard.Examples.cycle_transverseReservoir`, `R32-O20`). An explicit
positive-wait `GL₂(ℚ)` return family with `det M_n = (473/2240)(1−3ⁿ)` has a period-three orbit raising `v₁₃`
by `N` while lowering `v₂` by `13N`. Thus this determinant-valuation descent for `M₄(2)` fails at
the same projective-height amortization obstruction as the corresponding `M₃(2)` analysis. This
is a no-go for that proof method, not a reduction between the two full decision problems.

**The affine Collatz slice meets an open literature boundary.** The rank-(2,2) profile of
M₃(2) is generic projective incidence. Only its fixed affine Collatz slice is translated by
`R32-S41` into membership of a translation in `PK ⊆ Γ₆ = ℤ[1/6]⋊ℤ²`. This is not a
reduction of all GPI₂ to Γ₆. The literature audit in `reports/M.md` separates the decidable
one-dilation group ℤ[1/q]⋊ℤ from undecidable rational-subset membership in ℤ≀ℤ. Neither
result classifies Γ₆ or the fixed `PK` slice. The latter is neither recognizable (`R32-O21`)
nor in the cited flat class: it has determinant magnitudes tending to zero. These exclusions
do not determine its decidability.

## Integrated reductions

| Result | Lean | Cell interface |
| --- | --- | --- |
| Interface compression | `InterfaceCompression.isMortal_iff`, `.isMortal_rankOne_iff` (`MM-C06`) | each stated factored-cut instance → transition-only or bridge-path zero |
| Free-monoid rank-one-empty-return | `FreeMonoidReturn.physical_isMortal_iff_rankOneEmptyReturn` | `M₅(3)`,`M₄(3)`,`M₃(3)` |
| Four-mode artery `(4,2)` | `FourModeArtery.fourModePair_isMortal_iff_returnFamily` | `M₄(2)` |
| Prefix-transducer packing (CHHN Thm 4) | `PrefixPacking`; `UniversalNeary.codeHalts_reduces_mortality63` / `codeHalts_reduces_mortality122` | M₆(3), M₁₂(2) primitive-recursive endpoints |
| Skolem companion equivalence | `SkolemReduction.IntegerRecurrence.exists_term_eq_zero_iff_isMortal` | rational pair with a rank-at-most-one cut; no formal computability endpoint in this file |

The generated axiom inventory is `verification/axioms.txt`. Computability coverage is stated
per reduction; a pointwise equivalence is not silently promoted to a formal many-one endpoint.

## Obstruction theorems (new walls)

- The audited exact-role periodic families have rank-stratum floors above eight at the
  tested periods and under the stated radix-digit deformation (`MM-O34`). The fixed-body
  rank-two recompilation has geometric minimum eleven and period-four minimum sixteen
  (`MM-C08`). These are architecture-specific exclusions, not an eight-state lower bound.
- The reader and descent obstructions above.

## One correction found in the literature

`reports/H.md` gives a counterexample to Halava–Niskanen (TCS 2024), Lemma 6 as stated:
α = 29S and 29S − 35S + 21S = 15S. Theorems 7, 8, 11 use the affected argument; this
witness disputes the lemma, not those theorem statements. Their external integrality test also
cannot be replaced by the proposed persistent valuation poison: an opposite push repairs it.
No ordinary mortality reduction follows from that replacement. Repair is tracked in issue #15.

Current priorities belong to [FRONTIER.md](../FRONTIER.md#reconciled-mortality-priorities-2026-09-04).
The reported failures do not establish a decidable-or-M₃(2)-hard dichotomy for the lower table.

## Addendum: a projective slice is Collatz-hard

A second sub-wave attacked the located core from the decidability and Diophantine sides:

- `reports/K.md`: the two-dilation pointed-expansion carry is unbounded (`C_n ≥ ⌊k_n/18⌋`),
  killing a bounded-carry decision automaton for GPI₂.
- `reports/N.md`: `MixedRadixTape.unequalTailScaling_matrix_eq_zero` proves a single Möbius
  letter edits the mixed-radix digit string nonlocally, killing a local-rewrite tape encoding.
- `reports/S.md`: the bridge is an S-unit equation with `3^k` terms; ESS bounds solutions per
  fixed length but not the length, and the pure cubic `X³−N` normalizes via `M_{3q+r}=N^q M_r`
  to the residue problem `{M₀,M₁,M₂}`, whose one-singular stratum is again GPI₂. The non-pure
  cubic-reflection orbit remains a separate rank-`(3,2)` obstruction.

Construction, height descent, numeration, tape encoding, and Diophantine finiteness fail here
for the separate reasons recorded above. Their overlap is useful strategically, but does not
prove one universal obstruction or identify every open rank profile with GPI₂.

Shortcut Collatz embeds in GPI₂ (`R32-S37`, `ProjectiveCollatz.reachesOne_iff_shortcutCollatz`),
so a decision procedure for GPI₂ would decide pointwise shortcut-Collatz reachability. Through
the checked reverse compiler, the same lower bound applies to the rank-`(2,2)` profile of
`M₃(2)` and to `M₂(3)`. This is a one-way decision-theoretic lower bound. It neither proves GPI₂
undecidable nor obstructs an undecidability construction for a larger mortality cell. The exact
conclusion is local: a formal Collatz-hard projective slice recurs across several low-rank
analyses, while the remaining profiles and construction routes retain independent mathematical
content.
