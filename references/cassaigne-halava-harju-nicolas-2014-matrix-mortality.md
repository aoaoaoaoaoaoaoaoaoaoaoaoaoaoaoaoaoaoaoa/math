# Cassaigne–Halava–Harju–Nicolas (2014)

**Citation.** Julien Cassaigne, Vesa Halava, Tero Harju, and François Nicolas,
“Tighter Undecidability Bounds for Matrix Mortality, Zero-in-the-Corner Problems, and More,”
arXiv:1404.0644v3 [cs.DM], 5 September 2014.

- Canonical source: https://arxiv.org/abs/1404.0644
- Local PDF: `cassaigne-halava-harju-nicolas-2014-matrix-mortality.pdf`
- Retrieved: 2026-07-21
- SHA-256: `604d4ea43fe3bbe452f4b03c7bfff6431028ca0df0001a523ad00a39e9d471a5`

## Results used

- Table 5 records the then-minimal known mortality-undecidability antichain `M₃(6)`,
  `M₅(4)`, `M₉(3)`, `M₁₅(2)`
  and marks `M₃(5)` unknown.
- Lemma 7 gives the base-3 upper-triangular morphism `Ψ(u,v)` whose `(1,3)` entry vanishes
  exactly when the words over `{1,2}` agree.
- Section 3 records `GPCP(3)` and `GPCP(4)` as open. Theorems 1 and 6 reduce
  `GPCP⁺(k)` to `Z₃(k)` and its common-first-column restriction; Theorem 3 reduces
  `GPCP(k)` to `R₃(k+1)`.
- Proposition 4 gives the general rank-one reduction `Z_d(k) ≤ M_d(k+1)`.
- Proposition 3 gives `Z_d(k) ≤ R_{d+1}(k)`.
- Theorem 4 gives `M_d(hk+1) ≤ M_{kd}(h+1)`.
- Theorem 7 gives the structured trade
  `Z̊_d(hk+1) ≤ Z_{1+k(d-1)}(h+1)`.
- Its closest three-generator and four-generator bounds are `Z₅(3)` and `M₅(4)`;
  these are the cells improved to `Z₄(3)` and `M₄(4)` by paired-role compression.

## Audit notes

For the directly proved terminal equation `U(w)10^β=V(w)`, Proposition 4's outer product is
exactly `Ψ(10^β,ε)e₃e₁ᵀ`. Thus the algebraic construction is an instance of CHHN's established
GPCP-to-zero-to-mortality route. The new source theorem has four active GPCP generators and
feeds Theorems 3, 6, and 7 to improve the `Z` and `R` tables.

For the second result, CHHN supplies the definitions, neighboring bounds, and Proposition 4.
The paired-role anti-diagonal quotient and the common-fixed-column converse are not present in
CHHN; the prior-art investigation found no earlier `Z₄(3)` or `M₄(4)` theorem.

Notation hazard: `Z_d(k)` is scalar reachability with input row `L` and column `C`, asking
whether `LYC=0`. It is equivalent to a specified diagonal-entry problem but is not defined as
one. `R_d(k)` is the upper-right-corner problem.
