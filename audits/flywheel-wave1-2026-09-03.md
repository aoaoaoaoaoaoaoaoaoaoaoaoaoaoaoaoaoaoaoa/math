# Flywheel wave 1: shared interface barriers in the lower table

**Date:** 2026-09-03. **Method:** interface compression (`MM-C06`) decomposes the studied rank
profiles into transition-only and bridge-path problems indexed by their singular generators.
Twelve Sol-xhigh executors attacked those problems in isolated worktrees; each returned a
fixed-shape report. This audit reconciles them. Every claim names the Lean declaration or the
report it rests on.

## The meta-finding

Several undecided cells expose the same low-rank bridge mechanisms. Interface compression makes
that overlap exact at the level of each stated rank profile. It does **not** prove that every open
cell reduces to generic two-generator projective incidence, nor that the open cells are mutually
equivalent. The common projective slice is a hardness cone inside the table, not a collapse of the
whole frontier.

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

Within this two-counter design, the one surviving geometry is two cuts (two graph vertices), each
reader at its own prime with its own trap, cross-edges preserving both — lane `G`, still running.

**Decidability side — the same amortization wall.** The natural well-founded descent for the
unary return arteries (`M₄(2)^{(4,2)}`, `M₃(2)^{(3,2)}`), the total determinant valuation, is
refuted by exactly the transverse-reservoir cycle that already blocks `M₃(2)`
(`reports/D.md`; `ReturnGuard.Examples.cycle_transverseReservoir`, `R32-O20`). An explicit
`GL₂(ℚ)` return family with `det M_n = (473/2240)(1−3ⁿ)` has a period-three orbit raising `v₁₃`
by `N` while lowering `v₂` by `13N`. Thus this determinant-valuation descent for `M₄(2)` fails at
the same projective-height amortization obstruction as the corresponding `M₃(2)` analysis. This
is a no-go for that proof method, not a reduction between the two full decision problems.

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
| Interface compression | `InterfaceCompression.isMortal_iff`, `.isMortal_rankOne_iff` (`MM-C06`) | each stated factored-cut instance → transition-only or bridge-path zero |
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
2. Decision work on `M₂(3)` and the rank-`(2,2)` profile of `M₃(2)` concentrates on GPI₂. The
   metabelian gap (`reports/M.md`) leans that slice toward decidable: the undecidable wreath
   mechanism needs freely independent translates that `Γ₆`'s cyclic module lacks. Other cells
   retain construction routes not mediated by GPI₂.

## Addendum: a projective slice is Collatz-hard

A second sub-wave attacked the located core from the decidability and Diophantine sides:

- `reports/K.md`: the two-dilation pointed-expansion carry is unbounded (`C_n ≥ ⌊k_n/18⌋`),
  killing a bounded-carry decision automaton for GPI₂.
- `reports/N.md`: `MixedRadixTape.unequalTailScaling_matrix_eq_zero` proves a single Möbius
  letter edits the mixed-radix digit string nonlocally, killing a local-rewrite tape encoding.
- `reports/S.md`: the bridge is an S-unit equation with `3^k` terms; ESS bounds solutions per
  fixed length but not the length, and the pure cubic `X³−N` normalizes via `M_{3q+r}=N^q M_r`
  to the residue problem `{M₀,M₁,M₂}`, whose one-singular stratum is again GPI₂. The non-pure
  cubic-reflection orbit remains a separate rank-`(3,2)` obstruction.

With the construction wall (`W`) and the descent refutation (`D`), five methods — construction,
height descent, numeration, tape encoding, and Diophantine finiteness — encounter the same
unequal-radix nonlocality in overlapping projective-incidence strata. This convergence explains
several failed routes; it does not identify every open rank profile with GPI₂.

Shortcut Collatz embeds in GPI₂ (`R32-S37`, `ProjectiveCollatz.reachesOne_iff_shortcutCollatz`),
so a decision procedure for GPI₂ would decide pointwise shortcut-Collatz reachability. Through
the checked reverse compiler, the same lower bound applies to the rank-`(2,2)` profile of
`M₃(2)` and to `M₂(3)`. This is a one-way decision-theoretic lower bound. It neither proves GPI₂
undecidable nor obstructs an undecidability construction for a larger mortality cell. The exact
conclusion is local: a formal Collatz-hard projective slice recurs across several low-rank
analyses, while the remaining profiles and construction routes retain independent mathematical
content.
