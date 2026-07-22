# Rote (2024 full version)

**Citation.** Günter Rote, “Probabilistic Finite Automaton Emptiness Is Undecidable
for a Fixed Automaton,” arXiv:2412.05198v1 [cs.FL], 8 December 2024. Full version of
the peer-reviewed MFCS 2025 article.

- Canonical source: https://arxiv.org/abs/2412.05198
- Published version DOI: https://doi.org/10.4230/LIPIcs.MFCS.2025.86
- Local PDF: `rote-2024-fixed-pfa-emptiness-full-version.pdf`
- Retrieved: 2026-07-21
- SHA-256: `4b2aac972712a57389afb785835e283c4fb81faf026e5d1f1a568de775542636`

## Relevant results

Section 2.8 and footnote 3 give the same terminal-pair statement and repair as the
MFCS version: in every primitive solution tile 5 occurs only at the end, after replacing
Neary's defective four-one suffix by `1^{|u|+99}`. Section 5.2 further states that the
deterministic tag-system computation gives at most one primitive solution, apart from
repetition.

Appendix B defines fixed-boundary GPCP and remarks that Neary's terminal pair has a special
role, but it does not observe that moving tile 5 into the right boundary leaves a
four-generator GPCP instance.

## Audit notes

This 28-page full version supplies useful appendices, but it does not expand the proof of
the `|u|+99` terminal repair beyond the published footnote or exhaust malformed comparable
residuals. The current project bypasses that claim: it proves the four-tile fixed-boundary
equivalence directly and supplies a fresh-marker fifth pair. This paper remains important
diagnostic and bibliographic context, but is no longer a proof dependency.
