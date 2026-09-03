Verdict: obstructed

Cells affected: `M₃(2)` rank-`(3,2)` only: the proposed S-unit decision fails. The pure cubic
slice remains subsumed by `GPI₂`; `GPI₂`, `M₃(2)`, and the advertised cascade remain open.

Lean: no new declaration (the falsifier fired before formalization). Existing exact boundary:
`CubicReturn.pairGenerator_isMortal_iff_residue` — `'MatrixMortality.CubicReturn.pairGenerator_isMortal_iff_residue' depends on axioms: [propext, Classical.choice, Quot.sound]`;
`CubicReturn.pureOneSingular_reverseEdgeScalars` — `'MatrixMortality.CubicReturn.pureOneSingular_reverseEdgeScalars' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Statement: With spectral projectors `E_i` and `C_i=VE_iU`, a length-`k` bridge is
`Σ_{i₁,…,iₖ}(rC_{i₁}⋯C_{iₖ}c)∏_j λ_{i_j}^{n_j}`. ESS therefore sees `3^k` coordinates.
For `X³+X²−1`, the only eigenvalue relation is `αβγ=1`; the cubic field itself has
Dirichlet unit rank one, while the three eigenvalues in the splitting field have rank two. The
wait-image group in `(G_m)^{3^k}` has rank `k`, and its Zariski closure is the Segre image of
`T^k`, `T={(α,β,γ):αβγ=1}`. For `X³−N`, the exact locus is the `3^k` torsion-coset
list `τ_ρΔ` (`ρ∈(ℤ/3)^k`, `Δ={(t,…,t)}`): `M_{3q+r}=N^qM_r`, so every zero lift is
the same residue point after projective normalization, and ESS counts that point rather than
the word length. The residue problem is mortality of `{M₀,M₁,M₂}`, with the one-singular
stratum exactly `GPI₂`, not a one-variable equation. Coefficient-induced degenerate loci are
the intersections with proper-subsums of the displayed `3^k`-term form; they depend on `k` and
the tensors `C_i`, so there is no fixed finite subtorus list. The transverse reservoir lies on
`T_guard={(1,t⁻¹,t)}`. It is immortal, hence on no zero locus, and its repeated word changes
`k`; it does not contradict ESS.

If obstructed: the sharp surviving equation is the expansion above. ESS gives only
`#nondegenerate ≤ exp((6·3^k)^(3·3^k)(k+1))`; an effective fixed-`k` S-unit solver or Baker
bound still supplies no bound on `k`. Closure requires a uniform bounded-term compression or an
independent bridge-length descent.

DAG metadata: `S-O01` — obstruction / ESS attack on `MM-C06` and `R32-O16` / exact symbolic
computation, existing Lean reduction, and [ESS02](../references/evertse-schlickewei-schmidt-2002-multiplicative-linear-equations.md) / reported.

Next

- Retire S-unit effectivity until a bounded-term or bounded-length theorem exists.
- Keep the pure cubic slice under `GPI₂`; do not reopen it as rank-one Diophantine search.
- Attack the non-pure recurrence-digit continuant (`R32-O23`) by descent or a finite nucleus.
