# Nicolas (2008)

**Citation.** François Nicolas, “(Generalized) Post Correspondence Problem and
semi-Thue systems,” arXiv:0802.0726v5 [cs.DM], 12 November 2008.

- Canonical source: https://arxiv.org/abs/0802.0726
- Local PDF: `nicolas-2008-gpcp-semi-thue.pdf`
- Retrieved: 2026-07-21
- SHA-256: `a67466e4a1ad9d49ebd529dfbc5fc0262dd87948740c54bfbd08b2257ba4fbbf`

## Results used

Nicolas defines `GPCP(k)` using two morphisms on a `k`-letter source alphabet and four
fixed boundary words, with a witness in the free monoid (so the empty witness is allowed).
He proves the standard reductions linking bounded GPCP, bounded PCP, and bounded-rule
semi-Thue accessibility. Section 1.3 records `GPCP(2)` as decidable and `GPCP(5)` as
undecidable, leaving `GPCP(3)` and `GPCP(4)` open.

For the present campaign this fixes the counting convention. Neary's four ordinary pairs,
together with the directly proved right boundary equation `U(w)10^β=V(w)`, form a
Nicolas-style four-generator GPCP instance with empty left boundaries and lower right boundary.
The fresh-marker five-pair repair supplies the equivalent primitive-terminal presentation but
is not needed to define the GPCP instance.

## Audit notes

The local PDF is arXiv v5. Its title page displays “March 1, 2022,” but the arXiv record
states that v5 was submitted on 12 November 2008; the latter is used bibliographically.
The paper predates both Neary's five-pair construction and Rote's correction, so its open
status is a historical baseline rather than evidence that the four-generator case remained
open after 2025.
