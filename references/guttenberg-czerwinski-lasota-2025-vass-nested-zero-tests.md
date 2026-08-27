# Guttenberg, Czerwiński, and Lasota (2025): VASS with Nested Zero Tests

**Citation.** Roland Guttenberg, Wojciech Czerwiński, and Sławomir Lasota, “Reachability and
Related Problems in Vector Addition Systems with Nested Zero Tests,” *40th Annual ACM/IEEE
Symposium on Logic in Computer Science (LICS)*, 2025, pp. 581–593.

- Work identity: DOI `10.1109/LICS65433.2025.00050`; arXiv `2502.07660`
- Canonical source: https://arxiv.org/abs/2502.07660
- Local artifact: none; no third-party redistribution grant was located
- Version and status: arXiv v2, 19 May 2025; peer-reviewed LICS 2025 paper and full version
- Retrieved: 2026-08-10
- SHA-256: `e86eb337e11c7ace88b7364c9612c8d7fe384036d2bca97c141397f1ea68020d`
  for the inspected arXiv v2 PDF; bytes not retained
- Access and retention: arXiv's standard distribution license permits platform distribution but
  supplies no clear onward-redistribution license; the IEEE publication is access-restricted
- Synopsis basis: complete text of arXiv v2 inspected from an ephemeral verified PDF extraction

## Synopsis

A vector addition system with nested zero tests (VASSnz) may test an initial segment of its
ordered counters for zero: testing counter `i` simultaneously tests every counter of lower
priority. The paper gives an Ackermannian upper bound for reachability in this model and a
primitive-recursive bound when dimension is fixed. Corollary V.7 states reachability for VASSnz
in the fast-growing class `Fω`.

The proof converts VASSnz into monotone extended VASS whose transitions belong to a suitable
relation class, constructs asymptotic overapproximations through a KLM-style decomposition, and
uses these approximations to decide reachability. The framework also decides boundedness,
semilinearity, separability, and several related reachability-set questions at stated
fast-growing complexity bounds. The paper presents this as a uniform geometric framework rather
than a reachability-only construction.

The priority restriction is essential to the model: zero-test sets are nested initial segments,
not arbitrary or incomparable subsets of counters. The results do not decide general VASS with
unrestricted zero tests.

## Source Assessment

The inspected v2 identifies the LICS paper as the conference version and contains the full proof.
No correction, withdrawal, or version conflict was found. Because no reusable distribution
license was located, only metadata, the exact inspected digest, and this synopsis are retained.

## Project Use

The reachability theorem supplies the external decision result for priority-affine residual
atlases whose guarded translations compile to VASSnz transitions. The project relies only on the
nested-zero-test reachability conclusion, not on the sharper complexity analysis.
