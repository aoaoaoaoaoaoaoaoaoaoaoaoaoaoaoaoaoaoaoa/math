Verdict: discovered

Cells affected: `M₅(3)`, `M₄(3)`, and `M₃(3)` remain open; their rank-one-empty-return reduction is now formalized without split or nonempty-return-unit hypotheses.

Author: GPT-5.6 Sol; elicited by @eternalism_4eva.

Lean:
- `FreeMonoidReturn.physical_isMortal_iff_rankOneEmptyReturn`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.physical_isMortal_iff_rankOneEmptyReturn_of_transitionUnits`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.empty_return`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.positiveReturn_isUnit`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.thrust`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.recoil`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.thrust_mul_recoil`: `[propext, Classical.choice, Quot.sound]`
- `FreeMonoidReturn.ToricCycle.zero_recoil_repaired`: `[propext, Classical.choice, Quot.sound]`

Statement: Over a field, for finite ambient and interface spaces, arbitrary transitions `X`, and one cut `UO` satisfying `OU=crᵀ`, mortality is equivalent to transition-only mortality or `rᵀR_{w₁}⋯R_{wₖ}c=0` for some `k≥0` and nonempty transition words `wᵢ`. Unit transitions remove the first disjunct. The `R_w` may be singular or zero.

If discovered: `R32-O15` does not extend to all monomial two-generator return monoids. With
`A=diag(3,1,1,1)`, `B=diag(3,4,1,1)`,
`U=[[1,0],[0,1],[-1,0],[0,0]]`, and
`O=[[1,0,1,0],[0,1,0,0]]`, one has `OU=diag(0,1)` and
`R_w=diag(3^|w|−1,4^#B(w))`, hence every nonempty return is a unit. On `[2ⁿ,1]`, `R_A` increments and `R_B` decrements projectively, while `R_AR_B=4I`. The same equation repairs recoil at zero, so the updater cannot supply permanent poison. `ReturnGuard` supplies exact reading, pole poisoning, and a trap separately; assembly failed.

Axiom snapshot diff: ten new entries, each exactly `[propext, Classical.choice, Quot.sound]`.

DAG metadata: free-monoid reduction / independent / formalized / active; four-mode cycle / independent / formalized / stock; zero-recoil repair / independent / formalized / obstruction-to-ansatz.

Next:
- Couple a two-place valuation reader to an updater whose poison prime never occurs in any return numerator.
- Make word order carry finite control, then prove the arbitrary-word converse.
