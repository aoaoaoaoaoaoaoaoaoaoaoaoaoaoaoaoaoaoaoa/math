# Diekert and Walter (2016)

**Citation.** Volker Diekert and Tobias Walter, “Characterizing Classes of Regular
Languages Using Prefix Codes of Bounded Synchronization Delay,” in *43rd International
Colloquium on Automata, Languages, and Programming (ICALP 2016)*, LIPIcs 55,
article 129, 2016.

- DOI: https://doi.org/10.4230/LIPIcs.ICALP.2016.129
- Canonical source: https://arxiv.org/abs/1602.08981
- Local PDF: `diekert-walter-2016-synchronization-delay.pdf`
- Retrieved: 2026-07-24
- SHA-256: `b4cf75cc22770f7400e7ab2cdaebe5d22e28f39fe080149c187e05a5ae18a7fc`

## Results used

The paper develops prefix codes of bounded synchronization delay as an algebraic
description of regular-language classes and relates them to local Rees products. It supplies
the correct vocabulary for a context code that eventually recovers its parsing phase.

This does not solve the malformed-word obligation in GPCP or mortality. A bounded-delay
code normally defines a constrained language; `GPCP(3)` quantifies over the entire source
free monoid. Every word outside the intended code must therefore be proved harmless by the
morphisms and boundaries.

## Audit notes

The local file is the arXiv version, which is longer than the CC-BY LIPIcs proceedings
version. We use only its code-theoretic definitions and scope.
