# Flywheel wave 1: the lower table collapses to the projective core

**Date:** 2026-09-03. **Method:** interface compression (`MM-C06`) reduces every open cell to
bridge-path problems indexed by the ranks of its singular generators. Twelve Sol-xhigh executors
attacked those problems in isolated worktrees; each returned a fixed-shape report. This audit
reconciles them. Every claim names the Lean declaration or the report it rests on.

## The meta-finding

The undecided cells are not independent. Under interface compression they all reduce to two
mechanisms, and both were shown to bottleneck on the two-generator projective core `M₂(3)` /
`M₃(2)`.

**Undecidability side — the two-counter wall.** Simulating a two-counter machine inside a low
-dimensional matrix semigroup with `p`-adic-enforced legality requires two independent registers,
a permanent poison on an illegal read, and reads that preserve the other register and the
control. This is impossible in the geometries below dimension six:

- On `P¹` (one rational coordinate) two registers cannot coexist: reading one moves the other's
  center (`reports/B.md`; `reports/C.md`, four-mode rail `FourModeArtery.railbreaker_*`).
- A pole-based zero test cannot be a unit-determinant isometry at the poison prime: a genuine
  finite pole forces the trap prime to divide the determinant
  (`TwoPlaceReader.integralFinitePole_breaks_negative`, `AlternatingReaderPoison.*`).
- On `P²` with one cut the two readers cannot share a nonzero empty return
  (`TwoRegisterPlaneNoGo.no_common_scaled_xReader_yReader_of_xPoleAtOne`).

The one surviving geometry is two cuts (two graph vertices), each reader at its own prime with
its own trap, cross-edges preserving both — lane `G`, still running.

**Decidability side — the same amortization wall.** The natural well-founded descent for the
unary return arteries (`M₄(2)^{(4,2)}`, `M₃(2)^{(3,2)}`), the total determinant valuation, is
refuted by exactly the transverse-reservoir cycle that already blocks `M₃(2)`
(`reports/D.md`; `ReturnGuard.Examples.cycle_transverseReservoir`, `R32-O20`). An explicit
`GL₂(ℚ)` return family with `det M_n = (473/2240)(1−3ⁿ)` has a period-three orbit raising `v₁₃`
by `N` while lowering `v₂` by `13N`. So deciding `M₄(2)` by descent is at least as hard as the
projective-height amortization that `M₃(2)` needs; `M₄(2)` is **not** an easier decidability
target than `M₃(2)`.

**The core itself is at an open literature boundary.** The rank-`(2,2)` artery of `M₃(2)` is
generic projective incidence `GPI₂`, which `R32-S41` reduces to rational-subset membership of a
translation in `PK ⊆ Γ₆ = ℤ[1/6]⋊ℤ²`. `reports/M.md` locates this precisely: decidable for one
-dilation `ℤ[1/q]⋊ℤ` (Cadilhac–Chistikov–Zetzsche, ICALP 2020), undecidable for `ℤ≀ℤ`
(Lohrey–Steinberg–Zetzsche 2015); `Γ₆` sits between (two multiplicatively independent cursors,
cyclic characteristic-zero module), and the `PK` slice is neither recognizable (`R32-O21`) nor
DPS-flat (determinants `2⁻ⁿ`). The status is open in the current literature.

## Validated reductions (to integrate into the main branch and the DAG)

| Result | Lean | Cell interface |
| --- | --- | --- |
| Interface compression | `InterfaceCompression.isMortal_iff`, `.isMortal_rankOne_iff` (`MM-C06`) | every cell → bridge paths |
| Free-monoid rank-one-empty-return | `FreeMonoidReturn.physical_isMortal_iff_rankOneEmptyReturn` | `M₅(3)`,`M₄(3)`,`M₃(3)` |
| Four-mode artery `(4,2)` | `FourModeArtery.fourModePair_isMortal_iff_returnFamily` | `M₄(2)` |
| Prefix-transducer packing (CHHN Thm 4) | `sol-E`: generalized `PrefixMortality`; `mortality63`/`mortality122` primrec endpoints | `M₆(3)`,`M₁₂(2)` formal |
| Skolem → `M_d(2)` | `sol-E`: Skolem-reduction | Skolem wall on `d ≥ 5` |

All carry exactly `[propext, Classical.choice, Quot.sound]`.

## Obstruction theorems (new walls)

- Periodic and rank-two same-role compression cannot reach `M₈(2)`: certified DFT-rank floors
  `≥ 9` for every period `4..8`, invariant under injective radix-digit deformation
  (`reports/A.md`,`A2`; `PeriodicReturn.*`, `RankTwoRecompile.*`, floors in
  `tools/audit_periodic_dft_floor.py`). `M₈(2)` needs a changed early return or a genuinely
  new mechanism, not a recompiled role set.
- The two-counter and descent walls above.

## One correction found in the literature

`reports/H.md`: Halava–Niskanen (TCS 2024) Lemma 6 is false as stated; explicit counterexample
`α = 29S`, `29S − 35S + 21S = 15S`. Theorems 7, 8, 11 depend on it. Their integrality test is
also not internalizable as `p`-adic poison (an opposite push heals the trap), so it yields no
ordinary mortality reduction. This is an external-correspondence item, not a project result.

## Where the beam points next

1. `G` (two-cut two-vertex machine) is the last live low-dimension undecidability construction.
   Success closes `M₅(3)` or `M₄(3)`; a clean failure is the structural theorem "no `p`-adic
   two-counter machine in dimension `≤ 5`", strong evidence the lower table is
   decidable-or-`M₃(2)`-hard.
2. Everything else concentrates on `M₂(3)`/`M₃(2)`. The metabelian gap (`reports/M.md`) leans
   the `M₂(3)` prior toward decidable: the undecidable wreath mechanism needs freely independent
   translates that `Γ₆`'s cyclic module lacks.
