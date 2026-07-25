# Fazekas and Seki (2023)

**Citation.** Szilárd Zsolt Fazekas and Shinnosuke Seki, “Freezing 1-Tag Systems with
States,” *Electronic Proceedings in Theoretical Computer Science* 386, pp. 82–95, 2023.

- DOI: https://doi.org/10.4204/EPTCS.386.8
- Canonical source: https://arxiv.org/abs/2309.02753
- Local PDF: `fazekas-seki-2023-freezing-one-tag-states.pdf`
- Retrieved: 2026-07-24
- SHA-256: `34523d602365d7ed3e2d988c1cd41eb4c586a1cf332e1c39272edfea67e9ba6e`
- License: Creative Commons Attribution

## Results Used

Section 2 defines a one-tag system with states by a finite tape alphabet `Γ`, state set `Q`,
and transition function

```text
δ : Q × Γ → Q × Γ*.
```

One step deletes the front symbol, changes state, and appends the selected word. The paper
also records the equivalent circular-tape interpretation. This is the source model matched by
the two-state pushout compiler in [`M4-C01`](../SALVAGE.md#m4-c01-two-state-pushout-compiler).

The introduction states that unrestricted one-tag systems with states simulate Turing machines
and attributes the result to Zaiontz's 1976 circular-automata paper. It supplies no bound of two
states or two tape symbols. The present campaign relies only on the model definition and on the
absence of the required small bound from this paper; it does not treat the cited universality
statement as proved here.

## Audit Notes

The paper's theorems concern the freezing restriction, under which each cell is rewritten only
a bounded number of times. That restriction is not the proposed universal source. Its
undecidability results for freezing systems concern language emptiness, universality, and
equivalence through PCP encodings, not halting of a fixed binary two-state queue system.

The arXiv record has one version, submitted 6 September 2023, and identifies the EPTCS
publication. The local PDF is the CC-BY arXiv copy. Zaiontz 1976 was not located in a
lawfully redistributable primary copy during this audit; its universality claim remains a
source-level follow-up obligation.
