Verdict: obstructed

Cells affected: No closure of `M₈(2)`, `M₇(2)`, or `M₆(2)`. The exact-role periodic lane is excluded at every requested period by the following certified DFT-rank floors (rows are periods):

| family | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|
| paired | ≥12 | ≥14 | ≥12 | ≥19 | ≥12 |
| `M₃(5)` | — | ≥10 | ≥9 | ≥13 | ≥10 |

`tools/audit_periodic_dft_floor.py` exhausts all surjective assignments and rationally feasible cyclotomic zero-orbit patterns. The table gives exact minima of this rank-stratum relaxation, not exact DFT minima.

Lean:
- `#print axioms PeriodicReturn.pairGenerator_isMortal_iff_residue` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms PeriodicRankScreen.pairedComponent_three_le_rank` — `[propext, Classical.choice, Quot.sound]`
- `#print axioms PeriodicRankScreen.nearyComponent_two_le_rank` — `[propext, Classical.choice, Quot.sound]`

The `verification/axioms.txt` diff adds exactly these three outputs.

Statement: Over a field, for positive `m`, nonzero `ν`, finite indices, and nonempty ambient index, `A^m=νI` implies `IsMortal (pairGenerator A (U*O)) ↔ IsMortal (k : Fin m ↦ O*A^k*U)`. In characteristic zero, paired components with nonzero toggle, separator, and `q` have rank ≥3; `M₃(5)` components with nonzero terminal and ordinary parts have rank ≥2. The first theorem is false at `m=0` (`ν=1`, `A=0`).

If obstructed: `N_min ≥ 9` throughout both tables. Escape requires leaving the lawful periodic radix-digit deformation family, forbidden by A2's stop rule.

DAG metadata: return equivalence — reduction / agentic / Lean-checked / graduated; rank strata — obstruction / agentic / Lean-checked / active; DFT floors — obstruction / agentic / exact symbolic / active.

Next:
- Formalize rational DFT descent/rank-optimal realization.
- Do not extend the deformation search; A2 stopped it.

## A2

The injective radix-digit deformation leaves the certified floors unchanged:

| family | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|
| paired | ≥12 | ≥14 | ≥12 | ≥19 | ≥12 |
| `M₃(5)` | — | ≥10 | ≥9 | ≥13 | ≥10 |

Exact symbolic rerun: `tools/audit_periodic_dft_floor.py`. At integer `a≥2`, paired certificates acquire positive radix factors and `d₀-d₁`; Neary adds `code(0001)`, nonzero by injectivity against the empty word. Every floor exceeds eight, so A2 stops. DAG metadata: radix screen — obstruction / agentic / exact symbolic / active.
