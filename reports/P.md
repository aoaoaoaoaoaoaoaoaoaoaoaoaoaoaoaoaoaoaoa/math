Verdict: obstructed

Cells affected: `M₄(3)^(4,4,3)` and `M₅(3)^(5,5,3)` remain open; no upward closure follows.

Author: GPT-5.6 Sol; elicited by @eternalism_4eva.

Lean:
- `TwoRegisterPlaneNoGo.no_common_scaled_xReader_yReader_of_xPoleAtOne`: `[propext, Classical.choice, Quot.sound]`
- `TwoRegisterPlaneNoGo.cut_sq_eq_zero_of_emptyReturn_eq_zero`: `[propext, Classical.choice, Quot.sound]`
- `TwoRegisterPlaneNoGo.zero_emptyReturn_forces_mortal_cut`: `[propext, Classical.choice, Quot.sound]`

Statement: In homogeneous coordinates `[x:y:z]`, let an embedded `x`-reader have rows `[[a,0,b],[0,s,0],[c,0,d]]`, with nonzero projective scale `σₐ` and genuine pole at one (`c≠0`, `c+d=0`), and let a mirrored `y`-reader have rows `[[t,0,0],[0,a′,b′],[0,c′,d′]]`, with arbitrary scale `σᵦ`. They cannot be the same empty return. This is independent of the diagonal modes and ambient dimension. If the empty return `OU` is instead forced to zero, then `(UO)²=U(OU)O=0`, so the cut alone is mortal.

If obstructed: the sharp equation is `σₐc=(R_∅)₂₀=0`, forced by the mirror block, contradicting `σₐc≠0`. Repair requires abandoning a common nonzero empty return: use a non-pole zero test, a non-mirrored chart, or multiple cuts. No finite `N` makes the stated one-cut linear system feasible; tasks 2–3 therefore do not open.

Axiom snapshot diff: three entries, each exactly `[propext, Classical.choice, Quot.sound]`.

DAG metadata: two-reader empty-return wall / P, MM-C06 / Lean / obstructed; zero-empty-return cut square / P, MM-C06 / Lean / validated.

Next (max 3 bullets)

- Search only non-pole zero tests sharing a nonsingular empty return.
- If a second cut is admitted, budget its extra bridge vertex before testing arithmetic.
