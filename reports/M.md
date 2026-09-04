# M. Rational-subset membership in `Γ₆`

Verdict: obstructed. The status of `RatSubMem(Γ₆)` and of the fixed `PK` slice is open as of 2026-09-03.

Cells affected: none closed. `GPI₂`, the rank-`(2,2)` artery of `M₃(2)`, and `M₂(3)` remain open; full `M₃(2)` also retains its independent rank-`(3,2)` artery.

Lean: none; the open-status falsifier forbids a new reduction. Gate: `lake build -j 2` failed before building because Lake 5.0.0 rejects `-j`; `LintAudit.lean` and `AxiomAudit.lean` passed, and `diff -u verification/axioms.txt <(lake env lean AxiomAudit.lean)` was empty.

Statement: [CCZ20, Theorems 3.1–3.3](https://doi.org/10.4230/LIPIcs.ICALP.2020.116) decide full rational-subset membership for the one-dilation group `ℤ[1/q]⋊ℤ` (PSPACE-complete; fixed-subset membership in logspace), and [GLZ23, Theorem 4.1](https://doi.org/10.1142/S0218196723500285) makes its knapsack problem NP-complete. At the opposite boundary, [LSZ15, Theorem 6](https://doi.org/10.1016/j.ic.2014.12.014) gives one fixed finitely generated submonoid of `ℤ≀ℤ` with undecidable membership, hence undecidable rational-subset membership, although knapsack is NP-complete ([GKLZ18](https://doi.org/10.4230/LIPIcs.STACS.2018.32)) and the ordinary Identity Problem is decidable for every finitely generated metabelian group ([Dong24, Theorem 1.1](https://doi.org/10.1145/3618260.3649609)). `Γ₆=ℤ[1/6]⋊ℤ²` lies between these mechanisms: it has two multiplicatively independent cursor directions but a cyclic characteristic-zero module. The LS tiling construction needs freely independent translates ([LS11](https://doi.org/10.1007/s00224-010-9264-9)); Dong's successor decides submonoid membership only for finitely presented `𝔽ₚ[X₁±,…,Xₙ±]`-modules ([Dong25, Theorem 3.1](https://doi.org/10.4230/LIPIcs.ICALP.2025.154)). No located result classifies submonoid or knapsack membership in `Γ₆`.

If obstructed: `τ_N∈PK ⇔ N` reaches `1` under shortcut Collatz. `PK` is not recognizable: it is proper, while `R32-O21` makes every finite image full. It is not DPS-flat over `GL₂(ℤ)` or `S=GL₂(ℤ)∪{|det|>1}`: `K` contains determinants `2⁻ⁿ`, whereas every such flat expression has respectively finitely many determinant magnitudes or a positive lower bound ([DPS24, Definition 6.1 and Theorems 7.1–7.2](https://doi.org/10.1137/22M1512612)). A solution must control unbounded order-sensitive two-base translation sums; hardness must preserve `P*` followed by one parabolic subgroup, without inverse simulation.

DAG metadata: `M-O01` open `Γ₆` boundary — obstruction / literature / reported / active. `M-O02` `PK` fragment exclusion — obstruction / synthesis / audited / active.

Next:
- Seek a characteristic-zero cyclic-module analogue of pointed expansions.
- Monitor rational-subset and submonoid results for generalized metabelian Baumslag–Solitar groups.
- Reject hardness transfers lacking the exact positive-`P`/single-`K` language.
