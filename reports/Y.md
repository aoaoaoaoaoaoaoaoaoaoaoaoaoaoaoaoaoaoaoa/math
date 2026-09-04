Verdict: discovered

Cells affected: `M₈(2)` remains open. The sole rank-two recompilation validated in this run has geometric Hankel minimum 11 and period-four minimum 16, so this lane meets the stated ≥9 falsifier and stops.

Lean:
- `#print axioms RankTwoRecompile.toggle_rank` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms RankTwoRecompile.dataB_rank` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms RankTwoRecompile.dataC_rank` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms RankTwoRecompile.separator_rank` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms RankTwoRecompile.coefficient_eq_zero_iff_paired` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms GuardedTwoStateLift.allWords_sameZero_iff_data_c_gate` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms ChangedSeparatorTail.tiltedTernaryCode_injective` — `[propext, Classical.choice, Quot.sound]`

Statement: Over `ℚ`, at `β=3` and body `bcbcbb`, adjoining a silent coordinate to `G3-C07` gives four-dimensional roles `T′,D_b′,D_c′,P″` of exact ranks `4,3,2,1`; for every control word `w`, its coefficient is zero iff `pairedCoefficient ℚ 3 mixedBody w=0`. This is fixed-source, not polynomially source-uniform; it preserves the first axis, but `D_b′` scales and `D_c′` kills that axis. In the guarded singular-gate ansatz, the finite block and parity identities of `G3-C08` reduce uniform exactness to the sharp surviving incidence equation `g A_w q=0 ↔ pairedCoefficient ℚ β body (.data .c :: w)=0` for every `w`; tilted-code injectivity is a sufficient semantic discharge when those identities compute that code. The exact checker exhausts all 88,573 words through length 10 and checks four longer terminal witnesses. For unit role scales and unit geometric ratio, order ranks are `TBC=11, TCB=11`, and 12 otherwise; the minimum over all 24 period-four orders is 16.

If discovered: Rank profile `4/3/2/1` is attainable with complete arbitrary-word converse, so no four-dimensional rank-only analogue of `G3-S03` can prove task 4. Uniform source coding, not role rank, is the surviving obstruction.

DAG metadata: fixed-body recompilation — construction / `MM-C06,G3-C07` / Lean-checked / active; bounded and Hankel audit — obstruction / Y / exact rational / active; uniform gate criterion — reduction / `G3-C08,MM-C05` / Lean-checked / graduated.

The `verification/axioms.txt` diff adds exactly the five new `RankTwoRecompile` outputs. `RankTwoRecompile.lean` and its namespace lint pass; `scripts/check.sh` was not run, per the resumed-run hard rule. Authorship: GPT-5.6 Sol; elicited by @eternalism_4eva.

Next:
- Do not continue this lane: the ≥9 Hankel falsifier fired.
- Attack or exclude the uniform two-state incidence equation in its owning cell.
