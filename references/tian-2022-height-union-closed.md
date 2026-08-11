# Tian (2022): Union-closed sets of small or large height

**Citation.** Chenxiao Tian, “Union-closed Sets Conjecture Holds for Height
H(F) ≤ 3 and H(F) ≥ n − 1,” arXiv:2112.06659v2, 2022.

- Work identity: https://doi.org/10.48550/arXiv.2112.06659
- Canonical source: https://arxiv.org/abs/2112.06659v2
- Local artifact: `tian-2022-height-union-closed.pdf`
- Version and status: arXiv v2, revised 9 April 2022; preprint
- Retrieved: 2026-08-10
- SHA-256: `de555c8aa437320ffe115c18eeb552b15827a65e09b302ca8f874037999f1997`
- Access and retention: Creative Commons Attribution 4.0
- Synopsis basis: complete inspection of the eight-page v2 PDF

## Synopsis

For a finite union-closed family not containing the empty set, Tian defines its height by
repeatedly removing the inclusion-maximal layer. This height is the maximum cardinality of an
inclusion chain. The main theorem states that Frankl's conclusion holds when the height is at
most three or at least `n−1`, where `n` is the ground-set size.

The low-height proof treats heights one and two directly. For height three it splits according
to whether the family has more than `2n` members: the large case uses overlapping two-layer
“tent” subfamilies, while the small case invokes the Falgas-Ravry separating-family estimate.
The high-height case uses the known Frankl-complete status of one- and two-element member
sets.

## Source Assessment

This is an unrefereed preprint whose notation and prose require care. In particular, its stated
definition of “separating” is less precise than the standard exactly-one-of-two definition, and
several transitions in the height-three tent proof are compressed. Colbert's later
peer-reviewed theorem independently proves the corresponding dimension-two result for even
infinite union-closed families and explicitly identifies Tian's height-three case as its finite
predecessor.

## Project Use

The report audited in
[`frankl-counterexample-lunge-2026-08-10.md`](../audits/frankl-counterexample-lunge-2026-08-10.md)
rediscovered the consequence that a counterexample lattice cannot have rank three: delete the
bottom member, apply Tian's height-at-most-three theorem, and restore the bottom using
the strict inequality and integrality. The report supplies an independent incidence proof; no
priority is claimed for its rediscovered statement.
