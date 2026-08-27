# Ciobanu and Logan (2021): Variations on the Post Correspondence Problem for Free Groups

**Citation.** Laura Ciobanu and Alan D. Logan, “Variations on the Post Correspondence Problem
for Free Groups,” in Nelma Moreira and Rogério Reis, eds., *Developments in Language Theory,
DLT 2021*, Lecture Notes in Computer Science 12811, 90–102, Springer, 2021.

- Work identity: DOI
  [10.1007/978-3-030-81508-0_8](https://doi.org/10.1007/978-3-030-81508-0_8);
  arXiv:2104.05772
- Canonical source: https://link.springer.com/chapter/10.1007/978-3-030-81508-0_8
- Local artifact: `ciobanu-logan-2021-free-group-pcp-variations.pdf`
- Version and status: peer-reviewed accepted manuscript of the DLT 2021 publication
- Retrieved: 2026-08-11 from the Heriot-Watt University research portal
- SHA-256: `db740d6430811ee32ea88206ea7f631ebb70ca831a3ebd9df7022b80f302e988`
- Access and retention: author manuscript distributed by the institutional repository; final
  authenticated version is at the DOI
- Synopsis basis: complete inspection of the 13-page local artifact

## Synopsis

The paper relates the Post correspondence problem for free groups to several variants: the
generalized problem with four fixed boundary constants, rationally constrained PCP, the basis
and rank problems for equalizers, and restrictions involving injectivity or conjugacy
inequivalence. It tracks the source-alphabet rank through the reductions.

For free groups, generalized PCP was already known undecidable while ordinary PCP was open when
the paper appeared. The authors show that a basis algorithm for an equalizer with one injective
map decides rationally constrained PCP and, through an extreme-letter construction, generalized
PCP. Conversely, they reduce generalized instances satisfying explicit conjugacy exclusions to
ordinary PCP by adjoining two source generators. Conjugacy-inequivalent pairs are generic, so
this reduction applies generically rather than uniformly to every pair and boundary choice.

The paper also proves that rank and basis computation are equivalent for equalizers with one
injective map: given the rank, a Goldstein--Turner derived-graph construction recovers a basis.
Its reduction summary preserves the two-generator overhead between ordinary and generalized
PCP. Separately, it gives an undecidable rational constraint for free-group PCP and decidability
when both maps are noninjective.

None of these transformations eliminates fixed boundaries for an arbitrary rank-two source
without hypotheses. The extreme-letter and conjugacy guards introduce signed free-group words;
they do not produce an all-positive binary free-monoid converse.

## Source Assessment

The local artifact is the peer-reviewed accepted manuscript and includes the published citation
and DOI. Its status tables predate Carvalho's 2026 proof that unrestricted free-group PCP is
undecidable; the reduction theorems and rank accounting are unaffected by that supersession. No
correction or retraction is known from the inspected record.

## Project Use

The paper shows that fixed-boundary free-group equality is a genuine generalized-PCP seam and
records the exact two-source-generator overhead of known boundary-removal reductions. It does
not settle the positive binary fixed-boundary equation required by the current `M₄(3)` route.
