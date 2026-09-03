Verdict: obstructed

Cells affected: No closure of `M₈(2)`, `M₇(2)`, or `M₆(2)`. The exact-role periodic lane is excluded at every requested period by the following certified DFT-rank floors (rows are periods):

| family | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|
| paired | ≥12 | ≥14 | ≥12 | ≥19 | ≥12 |
| `M₃(5)` | — | ≥10 | ≥9 | ≥13 | ≥10 |

`tools/audit_periodic_dft_floor.py` exhausts all surjective assignments and all rationally feasible cyclotomic zero-orbit patterns. These are sharp floors of the zero-support/rank-stratum relaxation, not proved exact minima; saturating the remaining minor ideals is still required to sharpen them.

Lean: `PeriodicReturn.pairGenerator_isMortal_iff_residue` — `[propext, Classical.choice, Quot.sound]`; `PeriodicRankScreen.pairedComponent_three_le_rank` — `[propext, Classical.choice, Quot.sound]`; `PeriodicRankScreen.nearyComponent_two_le_rank` — `[propext, Classical.choice, Quot.sound]`.

Statement: Over a field, for positive `m`, nonzero `ν`, and nonempty ambient index type, `A^m=νI` implies `IsMortal (pairGenerator A (U*O)) ↔ IsMortal (k : Fin m ↦ O*A^k*U)`, without split hypotheses. Over any characteristic-zero field, a paired benchmark Fourier component with nonzero toggle, separator, and `q` coefficients has rank at least three; an `M₃(5)` component with nonzero terminal coefficient and any nonzero ordinary coefficient has rank at least two. The requested theorem is false at `m=0` (`ν=1`, `A=0`).

If obstructed: `N_min ≥ 9` for every screened family and period. Escaping requires a precisely defined same-zero deformation that defeats the component minors; arbitrary “entries which may change” is not yet a mathematical parameter space.

DAG metadata: periodic return equivalence — compiler / agentic / formalized / graduated; component rank strata — obstruction / agentic / formalized / active; DFT floors — obstruction / computational / exact symbolic / active.

Next:
- Saturate the residual minor ideals to replace floors by exact minima.
- Define and exhaust a bounded same-zero deformation space.
- Formalize rational DFT descent/rank-optimal realization; only periodic mortality is formalized here.

## A2

The injective radix-digit deformation leaves the certified floors unchanged:

| family | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|
| paired | ≥12 | ≥14 | ≥12 | ≥19 | ≥12 |
| `M₃(5)` | — | ≥10 | ≥9 | ≥13 | ≥10 |

Exact symbolic rerun: `tools/audit_periodic_dft_floor.py`. At integer `a≥2`, paired certificates acquire positive radix factors and `d₀-d₁`; Neary adds `code(0001)`, nonzero by injectivity against the empty word. Every floor exceeds eight, so A2 stops. DAG metadata: radix screen — obstruction / agentic / exact symbolic / active.
