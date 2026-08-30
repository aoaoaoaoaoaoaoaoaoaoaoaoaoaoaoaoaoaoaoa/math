# Bizière and Czerwiński (2025)

**Citation.** Clotilde Bizière and Wojciech Czerwiński, “Reachability in
One-Dimensional Pushdown Vector Addition Systems Is Decidable,” *Proceedings of the 57th
Annual ACM Symposium on Theory of Computing* (STOC 2025), pp. 1851–1862, 2025.

- DOI: https://doi.org/10.1145/3717823.3718149
- arXiv: https://arxiv.org/abs/2411.02386
- Canonical retained source: https://arxiv.org/pdf/2411.02386v1
- Local PDF: `biziere-czerwinski-2025-one-dimensional-pvas.pdf`
- Version: arXiv v1, submitted 4 November 2024; 40 pages
- Retrieved: 2026-08-30
- SHA-256: `c63d875953ec8549c89df3f45de458f8463c1e6c092f6182eeea256631c3b0e0`
- Access and retention: CC BY 4.0
- Synopsis basis: full inspection of the model definitions and theorem statements, with bounded
  inspection of the proof architecture

## Synopsis

A one-dimensional grammar vector addition system is a context-free grammar whose terminals are
integers. A complete derivation is executable from a counter value when adding its terminal yield
from left to right never makes the counter negative. Its effect must equal the difference between
the specified source and target counters. This grammar model and one-dimensional pushdown vector
addition systems have effectively equivalent languages.

Theorem 1 proves decidability of reachability for arbitrary one-dimensional grammar vector
addition systems. The proof classifies grammar nonterminals as thin or branching, then effectively
replaces any input grammar by a thin grammar with the same reachability relation. Reachability for
thin grammars follows from the finite-index result of Atig and Ganty. The replacement has a stated
triply exponential size bound relative to the complexity of thin-grammar reachability.

The paper does not prove that one-dimensional GVAS reachability relations are semilinear; such
relations can already be nonsemilinear. It leaves an elementary upper bound open and proves only
that an elementary algorithm for thin grammars would lift to arbitrary one-dimensional GVAS.

## Source Assessment

The retained artifact is the sole arXiv version and predates the peer-reviewed STOC publication.
No correction, withdrawal, or version dispute was found. The project relies only on the model
definition and the published decidability theorem, not on a complexity bound or semilinearity.

## Project Use

The theorem decides the one-counter grammar constructed in the pure-phase fork audit. That grammar
has finite residue and component nonterminals, integer terminals, and no zero test, reset, or second
counter, so it lies literally within the paper's one-dimensional GVAS definition.
