Verdict: obstructed

Cells affected: `M₃(2)^(3,2)` and `M₄(2)^(4,2)` remain open; determinant-valuation descent is refuted already in dimension three, hence also after adjoining an unreachable fourth unit mode.

Author: GPT-5.6 Sol; elicited by @eternalism_4eva.

Lean:
- `ReturnGuard.Examples.cycle_decoded_orbit`: `[propext, Classical.choice, Quot.sound]`
- `ReturnGuard.Examples.cycle_not_physical_isMortal`: `[propext, Classical.choice, Quot.sound]`
- `ReturnGuard.Examples.cycle_transverseReservoir`: `[propext, Classical.choice, Quot.sound]`

`AxiomAudit.lean` diff against `verification/axioms.txt`: empty.

Statement: For a finite prime set `S`, the proposed potential is
`Φ_S(n₁,…,n_k)=Σ_j Σ_{ℓ∈S}v_ℓ(det(VA^n_jU))`; appending `n` changes it by exactly `Σ_{ℓ∈S}v_ℓ(det M_n)`. It is not projective: replacing `M_n` by `c_nM_n` adds `2v_ℓ(c_n)`. More decisively, take `A=diag(1,1/3,3)`, `U=[[0,1],[1,0],[1,−1]]`, and `V=[[953/2240,−953/2240,473/2240],[−1,1,0]]`. Then `rank(UV)=2`, every `M_n=VAⁿU` lies in `GL₂(ℚ)`, and `det M_n=(473/2240)(1−3ⁿ)`.

If obstructed: The exact nonterminal cycle
`−3/14 →[1] 117/400 →[2] 27/28 →[3] −3/14`
iterates with bounded height, but `Φ_{13}([1,2,3]^N)=N` while `Φ_{2}([1,2,3]^N)=−13N`. Thus valuation-raising returns recur without a height bound, the opposite valuation descends without a lower bound, and `k=3N` is unbounded. Tasks 2–3 stop; Bacik’s unary order-four theorem is never reached. Any repair needs a scale-invariant potential that excludes periodic transverse storage using first-hit terminality or aperiodicity.

DAG metadata:

| Result | kind / origin / assurance / status |
|---|---|
| Potential append law | identity / D / exact symbolic / validated |
| Periodic counterfamily | obstruction / R32-O20 / Lean + exact symbolic / graduated |
| Descent verdict | obstruction / D / audited consequence / refuted |

Next (max 3 bullets)

- Hand the displayed family to lane G as the required transverse-reservoir shape.
- Restrict any successor to first-hit terminal or aperiodic paths and a projectively normalized Cartan/height invariant.
