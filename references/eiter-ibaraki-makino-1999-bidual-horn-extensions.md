# Eiter, Ibaraki, and Makino (1999): Bidual Horn functions and extensions

**Citation.** Thomas Eiter, Toshihide Ibaraki, and Kazuhisa Makino, “Bidual Horn
functions and extensions,” *Discrete Applied Mathematics* 96–97 (1999), 55–88.

- Work identity: DOI [`10.1016/S0166-218X(99)00033-5`](https://doi.org/10.1016/S0166-218X(99)00033-5)
- Canonical source: https://www.sciencedirect.com/science/article/pii/S0166218X99000335
- Local artifact: none; the inspected author-hosted copy states no downstream redistribution license
- Inspected copy: https://www.kr.tuwien.ac.at/staff/eiter/et-archive/files/da4123.pdf
- Version and status: peer-reviewed publication; inspected 33-page author-hosted copy
- Inspected: 2026-08-08
- Inspected PDF SHA-256: `746a33dd07b97f32534de61aa78a6eda0de05e3e92cabcde393fb26257c99308`
- Access and retention: metadata only; no license permitting local redistribution was located
- Synopsis basis: complete full-text inspection, cross-checked against the publisher’s HTML text;
  some mathematical glyphs in the author copy extract imperfectly

## Synopsis

A Boolean function is *bidual Horn* when its false points are closed under conjunction and
its true points are closed under disjunction, equivalently when the function and its dual are
both Horn. The class properly contains positive Boolean functions. The paper studies
recognition, representation, dualization, and the interpolation of a partially defined Boolean
function `(T,F)` by a bidual Horn function.

Lemma 3.4 gives a pairwise condition on the terms of a Horn DNF for biduality, yielding a
polynomial recognition algorithm from a Horn DNF (Theorem 3.5). Section 4 shows that the
obvious disjointness of the union closure of `T` and the intersection closure of `F` is
necessary but not sufficient for a bidual Horn extension. It develops canonical Horn and
co-Horn terms, characterizes extension existence through a labelled bipartite graph
(Lemma 4.5), and gives polynomial algorithms both to decide existence (Theorem 4.6) and to
construct an extension (Corollary 4.8). The paper also proves hardness results for uniqueness
and shortest extensions and relates dualization to positive-function dualization.

## Source Assessment

The extension theory concerns interpolation on the same Boolean cube; it does not assert that
every Horn function embeds into a bidual or self-dual Horn function while preserving variable
frequencies. The simple closure-disjointness test has an explicit counterexample, so any use of
extension theory must check the stronger canonical compatibility condition. No source-level
correction was found during the present inspection.

## Project Use

The extension criterion and its counterexample delimit attempts to complete a Horn
counterexample to a bidual or self-dual one without destroying strict coordinate majorities.
