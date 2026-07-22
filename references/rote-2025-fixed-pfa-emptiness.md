# Rote (2025)

**Citation.** Günter Rote, “Probabilistic Finite Automaton Emptiness Is Undecidable for a
Fixed Automaton,” *50th International Symposium on Mathematical Foundations of Computer
Science (MFCS 2025)*, LIPIcs 345, article 86, 2025.

- DOI: https://doi.org/10.4230/LIPIcs.MFCS.2025.86
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.86
- Related full version: https://arxiv.org/abs/2412.05198
- Local PDF: `rote-2025-fixed-pfa-emptiness.pdf`
- Retrieved: 2026-07-21
- SHA-256: `67b1c1c0e6ee6f48593038a190a313392465ab19e7659c92e499ec8b0aba8678`

## Relevant results

Section 2.8 explicitly states that Neary's five-pair instances have a forced first pair and a
forced final pair; in every primitive solution, pair 5 occurs only in the final position. Footnote 3
identifies the flaw in Neary's `1111` argument and repairs it by replacing the terminal pair with
`(10^β 1^{|u|+99}, 1^{|u|+99})`. The justification is that the appendants force every
length-`|u|+1` factor of a reachable tag dataword to contain `b`, so the long unary delimiter
cannot occur inside an encoded live configuration.

Rote then uses the forced pair operationally: after reversing words, it merges that pair's matrix
into a boundary vector and removes it from the generator pool. Section 5.2 also records that the
underlying deterministic computation has at most one primitive solution, apart from repetition.

The paper does not state the resulting four-generator bounded-GPCP corollary.

## Audit notes

Rote's diagnosis is correct, but the printed long-block justification controls reachable tag
datawords and intended deletion phases rather than every malformed prefix-comparable residual.
For example, a wrong branch can leave the genuine halt residual while remaining comparable:

```text
↓10^β → ↓10 → ↑0^(β−2)1 → ↑1^(β−1).
```

This is not a counterexample to Rote's asserted property, but it exposes a missing exhaustive
invariant. The current project therefore does not rely on the long-block repair. It proves the
four-ordinary-tile fixed-boundary theorem directly and uses a fresh-marker fifth pair. Rote is
cited for the historical diagnosis and adjacent boundary-absorption context, not as a
load-bearing source theorem.
