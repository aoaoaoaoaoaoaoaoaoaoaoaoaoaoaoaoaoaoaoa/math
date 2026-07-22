# Four-Generator GPCP and Five-Matrix Mortality

This project proves that four-generator generalized Post correspondence is undecidable and,
consequently, that mortality is undecidable for at most five `3 × 3` integer matrices.

## Status

The former source conditionality is closed. The proof does not rely on Rote's incompletely
justified long terminal block. Instead, it proves directly that Neary's four ordinary PCP pairs
satisfy their fixed-right-boundary equation exactly when the restricted binary tag system halts.
An exhaustive zero-run parser forces every candidate word into deletion-width blocks; a generic
queue-history theorem excludes every malformed path. A fresh delimiter then gives a corrected
binary five-pair PCP family whose primitive solutions end in tile five.

The entire new source theorem, fresh-marker repair, GPCP bridge, and exact five-integer-matrix
equivalence are machine-checked in Lean 4. The remaining external mathematical theorem is
Neary's peer-reviewed Lemma 9 establishing undecidability of the restricted tag family. The
formal model has been checked against its exact deletion width, appendant length, and initial
queue.

The current mathematical conclusions are:

```text
GPCP(4) is undecidable.
M₃(5) is undecidable.

Minimal known mortality undecidability antichain:
M₃(5), M₅(4), M₆(3), M₁₂(2).
```

Four emitted matrices are nonsingular and upper triangular; the fifth is a nonzero integer
matrix of rational rank one.

**Author:** GPT-5.6 Sol, elicited by [@eternalism_4eva](https://x.com/eternalism_4eva).

Read:

- [index.html](index.html) for the standalone illustrated exposition;
- [paper/main.pdf](paper/main.pdf) for the eight-page proof;
- [AUDIT.md](AUDIT.md) for the adversarial proof audit;
- [FORMALIZATION.md](FORMALIZATION.md) for the theorem/file map;
- [FOUNDATIONS.md](FOUNDATIONS.md) for the Lean trust base and exact external boundary;
- [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for the pinned one-command verification snapshot;
- [NOVELTY.md](NOVELTY.md) for the prior-art search;
- [FRONTIER.md](FRONTIER.md) for the wider mortality campaign;
- [references/README.md](references/README.md) for the preserved local bibliography.

## Verification

The project pins Lean and mathlib to `v4.12.0`.

```sh
./scripts/check.sh
```

The build rejects every warning, automatic implicit variable, default mathlib environment-lint
failure, linter suppression, and known proof escape. The exact transitive axiom snapshot for
the publication-facing declarations contains only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. Frozen outputs are preserved under
[verification](verification/README.md).

## Principal Declarations

- `terminal_match_iff_tagHaltsFrom`: four ordinary tiles match iff the restricted tag system
  halts;
- `nearyPCP_solvable_iff_tagHaltsFrom`: corrected binary five-pair PCP solvability;
- `nearyPCP_primitive_terminal`: exact primitive-terminal property;
- `nearyGPCP_solvable_iff_tagHaltsFrom`: four-generator GPCP equivalence;
- `nearyGPCPPlus_solvable_iff_tagHaltsFrom`: explicit nonempty-witness GPCP equivalence;
- `nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom`: exact five-matrix equivalence;
- `NearyArithmeticEnvelope.mortality_iff_halts`: specialization to the arithmetic envelope
  containing Neary's padded compiler outputs;
- `nearyMortality_terminal_rank_eq_one`: exact exceptional-matrix rank.

## Novelty Caution

Neary's one-version 2013 preprint publicly claimed the same numerical `M₃(5)` result through
a claimed four-pair PCP theorem. That theorem was not retained in his refereed 2015 successor,
which explicitly left four-pair PCP open and derived only the six-matrix bound; subsequent
literature followed the latter. No formal withdrawal or published diagnosis of the precise
2013 defect was found, so this project calls the claim *superseded and unestablished*, not
retracted. Rank-one boundary absorption is also prior art. The defensible priority language is
“to our knowledge, the first valid proof of `GPCP(4)` and hence of the previously unestablished
`M₃(5)` case.”
