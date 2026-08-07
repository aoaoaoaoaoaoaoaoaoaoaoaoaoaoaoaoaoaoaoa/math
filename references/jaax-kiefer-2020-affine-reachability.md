# Jaax and Kiefer (2020): Affine reachability

**Citation.** Stefan Jaax and Stefan Kiefer, “On Affine Reachability Problems,” in
*45th International Symposium on Mathematical Foundations of Computer Science (MFCS 2020)*,
LIPIcs 170, article 48, 2020. DOI: 10.4230/LIPIcs.MFCS.2020.48.

- Work identity: https://doi.org/10.4230/LIPIcs.MFCS.2020.48
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2020.48
- Local artifact: `jaax-kiefer-2020-affine-reachability.pdf`
- Version and status: peer-reviewed MFCS 2020 proceedings version, 14 pages
- Retrieved: 2026-08-07
- SHA-256: `f763f69b816af37fec2a6e1baf70ac20293e4fb6ce002245b3ffd8c271ecbadf`
- Access and retention: Creative Commons Attribution 3.0; publisher PDF retained unchanged
- Synopsis basis: full-text inspection

## Synopsis

The paper studies one-register machines with affine updates and the corresponding upper-
triangular `2 × 2` matrix problems. Proposition 1 records the standard interreductions among
affine membership or point reachability and upper-triangular matrix membership, vector
reachability, or scalar zero-reachability. Theorem 3 proves PSPACE-completeness of reachability
for integer affine register machines.

Theorem 4 proves NP-completeness of mortality for integral `2 × 2` matrices whose determinants
belong to `{1,0}`, even with one singular matrix and shear-form nonsingular matrices. In the
upper-triangular setting, Theorem 12 reduces affine reachability over `ℚ` to vector reachability;
Theorem 13 proves NP-completeness of membership when both diagonal entries are nonzero; and
Theorems 16–17 relate unrestricted upper-triangular membership to scalar reachability.

The results show that one-dimensional affine dynamics have substantial exact arithmetic
content even when decidable special cases exist. The paper does not give a general decision
procedure for nondeterministic rational affine point reachability.

## Source Assessment

The retained object is the peer-reviewed proceedings paper and repeatedly points to a longer
version for omitted proofs. No correction or retraction was found. Complexity statements must
be kept separate from the unresolved general rational-affine reachability problem.

## Project Use

The `M₄(3)` audit uses the affine/matrix equivalence and scope boundary to test whether a proposed
projective coordinate genuinely closes before importing one-dimensional reachability results.
