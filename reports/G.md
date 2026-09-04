Verdict: obstructed

Cells affected: `M₅(3)` profile `(5,3,3)` and `M₄(3)` profile `(4,3,3)` remain open. The proposed two-cut route closes neither cell and yields no upward closure.

Author: GPT-5.6 Sol; elicited by @eternalism_4eva.

Lean:
- `#print axioms TwoVertexPlaneNoGo.xReaderTransfer_eq_modes` → `[propext, Classical.choice, Quot.sound]`
- `#print axioms TwoVertexPlaneNoGo.xReaderConstant_ne_vecMulVec` → `[propext, Classical.choice, Quot.sound]`

Statement: For cuts `Cᵢ=UᵢOᵢ`, MM-C06 gives the two-vertex bridges `Eᵢⱼ(n)=OᵢAⁿUⱼ`. For every rational `center`, `reset`, `low`, and `high`, the required projective-plane lift `diag(M(center,reset,low,high),1)` decomposes into reciprocal and expanding rank-one coefficients plus `Kₓ=[[0,0,−center],[0,1,0],[0,0,−1]]`; for every rational column `u` and row `v`, `Kₓ≠uvᵀ`. Thus a reader needs two coordinates at its constant eigenvalue. With `d,e≥2`, the four nonconstant modes `2⁻¹,2^(d−1),3⁻¹,3^(e−1)` are pairwise distinct, so the mirrored loop readers require `N≥2+4=6` before cross-edge constraints. The task-1 falsifier fires: the `N=5` and `N=4` solution spaces are empty. Rescaling to share `1/6` separates the two rank-two center coefficients and raises the lower bound to seven.

If obstructed: Every rank-one coefficient obeys `(uvᵀ)ᵧᵧ(uvᵀ)ᶻᶻ−(uvᵀ)ᵧᶻ(uvᵀ)ᶻᵧ=0`, whereas the same minor of `Kₓ` is `−1`. Escape requires `N≥6` and a two-dimensional constant eigenspace; cuts, mantissa invariants, trap transport, and protocol design cannot repair the missing mode. Two cuts evade the shared-empty-return wall from `P`, but do not escape the two-counter wall.

Axiom snapshot diff: two entries, each exactly `[propext, Classical.choice, Quot.sound]`.

DAG metadata: embedded-reader modal decomposition / G, MM-C06 / Lean / validated; dimension-six two-reader wall / G / exact symbolic computation plus Lean / obstructed.

Next (max 3 bullets)

- If revisited at `N=6`, solve the coupled cross-edge factorization before any valuation dynamics.
