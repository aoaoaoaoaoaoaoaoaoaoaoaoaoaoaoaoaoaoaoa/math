# Dong (2024): Semigroup algorithmic problems in metabelian groups

**Citation.** Ruiwen Dong, “Semigroup Algorithmic Problems in Metabelian Groups,” in
*Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024)*,
pp. 884–891, ACM, 2024. DOI: 10.1145/3618260.3649609.

- Work identity: DOI [10.1145/3618260.3649609](https://doi.org/10.1145/3618260.3649609);
  [arXiv:2304.12893](https://arxiv.org/abs/2304.12893)
- Canonical source: <https://arxiv.org/abs/2304.12893>
- Local artifact: `dong-2024-semigroup-algorithmic-problems-metabelian.pdf`
- Version and status: arXiv v1, 25 April 2023, 52-page full version of the peer-reviewed STOC
  2024 paper
- Retrieved: 2026-09-03
- SHA-256: `34ab6ecae5450183006b36f0335281e6e8b459c255187b8a33c31d06e433b0d9`
- Access and retention: author-posted arXiv version; no separate permissive license identified
- Synopsis basis: complete inspection of the retained v1 artifact

## Synopsis

Theorem 1.1 decides the Group Problem, Identity Problem, and Inverse Problem for finitely
generated subsemigroups of every finitely generated metabelian group presented by a finite
metabelian presentation. The reduction embeds the input effectively in `Y⋊ℤⁿ`, where `Y` is a
finitely presented `ℤ[X₁±,…,Xₙ±]`-module, and converts full-image identity words into the
existence of nonnegative Laurent-polynomial vectors satisfying module and support conditions.
The decision proof combines graph support, convex-face accessibility, module computation, and
real-algebraic positivity.

The theorem does not decide Semigroup or Submonoid Membership: those problems include a variable
target and are explicitly separated from the three identity/inverse questions. It supplies no
regular normal form for a generated submonoid and no rational-subset membership algorithm.

## Source Assessment

The retained artifact is the sole arXiv version and is substantially longer than the STOC
proceedings paper. The ACM record identifies the peer-reviewed publication and pagination. No
correction, withdrawal, or superseding version was found.

## Project Use

For `Γ₆=ℤ[1/6]⋊ℤ²`, Theorem 1.1 decides whether a finitely generated semigroup contains the
identity, but does not decide membership in the fixed rational subset `PK`. It therefore blocks an
invalid transfer from “Identity Problem” to “Submonoid Membership” without changing the open
parabolic-slice boundary.
