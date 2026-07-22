# Forster, Heiter, and Smolka (2018)

**Citation.** Yannick Forster, Edith Heiter, and Gert Smolka, “Verification of
PCP-Related Computational Reductions in Coq,” in *Interactive Theorem Proving*,
LNCS 10895, 253–269, Springer, 2018.

- DOI: https://doi.org/10.1007/978-3-319-94821-8_15
- Canonical preprint: https://arxiv.org/abs/1711.07023v2
- Formalization: https://github.com/uds-psl/coq-library-undecidability
- Local PDF: `forster-heiter-smolka-2018-pcp-reductions-coq.pdf`
- Retrieved: 2026-07-22
- SHA-256: `4ee44f4f74933cacf5bffa49b468f5bc5638e5ff2c978583ee269f9c1b4c3bb6`

## Results used

The paper and accompanying Coq development verify a computable reduction chain from
single-tape Turing-machine halting through string rewriting and modified PCP to PCP. The
formal proof isolates inductive invariants absent from many textbook correctness arguments.
Its data are constructive, so the translation functions are computational rather than arbitrary
classical witnesses.

For this project the development is a proof-engineering precedent and a source of invariant
patterns. It does not settle the bounded-source problem: its generic PCP compiler has an
instance-dependent number of pairs and therefore cannot replace the specialized path to
four-generator GPCP.

## Audit notes

The local file is arXiv v2, which incorporates the ITP 2018 publication metadata. The audited
Coq repository revision was `c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c`. Coq proof terms
are not directly reusable in Lean, and no code has been translated from this development.
