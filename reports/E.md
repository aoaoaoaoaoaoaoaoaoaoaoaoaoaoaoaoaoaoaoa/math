Verdict: validated

Cells affected: no cell; hygiene results feed the compression, transport, Skolem-wall, and rank-census DAG nodes.

Lean: every declaration below has `#print axioms` = `[propext, Classical.choice, Quot.sound]`; `verification/axioms.txt` adds exactly 72 audit lines.

Shrunk: `CubicReturn.pairGenerator_isMortal_iff_residue`; `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero`; `ReturnConvert.physical_isMortal_iff_positiveBridge`; `ReturnFamily.pairGenerator_isMortal_iff`; `ReturnFamily.pairGenerator_isMortal_iff_positiveBridge`; `ReturnFamily.rankOnePair_isMortal_iff`; `ReturnGuard.physical_isMortal_iff_positiveBridge`; `ReturnSquare.physical_isMortal_iff_returnProduct`; `ReturnSquare.physical_isMortal_iff_positiveBridge`; `TwoPlaneEdges.isMortal_iff_exists_edgeProduct_eq_zero`.

Rebased: `ReturnFamily.pairGenerator_isMortal_iff_returnFamily`.

Packing: `PrefixPacking.CompleteCode.machine_isMortal_iff_source`; `CHHNPrefixPacking.ternaryPack_isMortal_iff`; `CHHNPrefixPacking.binaryPack_isMortal_iff`; `restrictedPrefixGenerator_mortal_iff_normalized`.

Undecidability: `mortality63Pack_primrec`; `mortality122Pack_primrec`; `mortality63Pack_mortal_iff`; `mortality122Pack_mortal_iff`; `mortality35To63`; `mortality35To122`; `UniversalNeary.codeHalts_reduces_mortality63`; `UniversalNeary.mortality63_not_computable`; `UniversalNeary.codeHalts_reduces_mortality122`; `UniversalNeary.mortality122_not_computable`.

Skolem/census: `IntegerRecurrence.companion_isUnit`; `IntegerRecurrence.observer_dot_companion_pow_initial`; `IntegerRecurrence.exists_term_eq_zero_iff_isMortal`; `IntegerRecurrence.skolemDecision_of_mortalityDecision`; `RankCensus.finTwo_allUnit_immortal`; `RankCensus.finTwo_rankOne_isMortal_iff`; `RankCensus.finFour_rankTwo_isMortal_iff`; `RankCensus.finFour_rankOne_isMortal_iff`.

Statement: For any certified complete prefix code with finite state/alphabet/source types, exact root decoding, synchronizer, and `|Source|=s(|Letter|−1)+1`, packing over a nontrivial commutative semiring preserves mortality in dimension `s·d`; concrete primitive-recursive instances give `M₃(5)≤M₆(3)` and `M₃(5)≤M₁₂(2)`, while the existing common-image quotient gives `M₁₀(2)`. An integer recurrence of order `d+1` whose oldest-term coefficient is nonzero has an explicit rational companion in `GL_(d+1)`, with `oAⁿu=uₙ`, hence Skolem zero existence iff rank-one-pair mortality; any Boolean mortality decider yields a Skolem decider without a `Decidable` assumption. Over a field, unit-only `M₂(k)` families are immortal, mixed unit/rank-one families satisfy the stated scalar-incidence criterion, and the `(4,2)`/`(4,1)` profiles reduce to matrix returns/scalar Skolem respectively. Fixed-word edge reflection alone retains split hypotheses because its exterior factors are not loop-closed.

DAG metadata: compression / audit / Lean-checked / validated; prefix transport / literature+audit / Lean-checked / validated; Skolem reduction / literature / Lean-checked / validated; rank census / audit / Lean-checked / validated.

Next (max 3 bullets)
- Integrate these four records and transport edges into the registry.
- Attach the Skolem wall to every `d≥5` mortality frontier cell.
