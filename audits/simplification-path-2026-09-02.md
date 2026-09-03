# Simplification path across the mortality corpus

**Date:** 2026-09-02
**Scope:** the Lean corpus (`MatrixMortality/`, 374 modules), `SALVAGE.md`, `FRONTIER.md`,
`FORMALIZATION.md`, and the CHHN and Bacik references.
**Method:** declaration signatures and module docstrings of the 45 core modules were extracted
and read in full; the frontier-specific modules were read through their registry records and
the principal-declaration map. Every claim below names the Lean declaration or registry record
it rests on, or states that it is unverified.

The findings are ordered by leverage. The first is implemented and checked; the rest are
reductions, walls, or transport edges that follow from existing declarations with little or no
new mathematics, together with the frontier consequences they force.

## 1. One theorem owns every finite-rank compression

`MatrixMortality/InterfaceCompression.lean` (new, builds, passes the environment linters)
proves, over any commutative semiring, with arbitrary *transitions* `X_a` and *cuts*
`C_j = U_j O_j` factoring through interfaces of any dimension:

```text
{X_a} ∪ {C_j} mortal
  ⟺ {X_a} mortal  ∨  ∃ nonempty path,  (O_{j₀}X_{w₁}U_{j₁})(O_{j₁}X_{w₂}U_{j₂})⋯ = 0.
```

Proof: a physical word with a cut is `X_{w₀}C_{j₁}X_{w₁}⋯C_{j_m}X_{w_m}`; multiplying by
`O_{j₁}` on the left and `U_{j_m}` on the right turns both exterior transition words into loops
of the bridge path. A zero bridge path spells the zero physical word `C_{j₀}X_{w₁}C_{j₁}⋯C_{j_m}`.
No splitting, rank, field, or nonvanishing-power hypothesis enters (`isMortal_iff`). With
rank-one cuts over a field the path is scalar (`isMortal_rankOne_iff`):

```text
{X_a} ∪ {c_j r_j} mortal  ⟺  {X_a} mortal ∨ ∃ j w j',  r_j X_w c_{j'} = 0.
```

What it subsumes, with the hypotheses the existing statements carry and do not need:

| Existing declaration | Record | Instance | Hypotheses now known to be artifacts |
| --- | --- | --- | --- |
| `mortal_adjoin_outer_iff` | MM-C01 | one rank-one cut | none (field only) |
| `ReturnFamily.pairGenerator_isMortal_iff` | R32-S01 | one transition, one cut | `left_inverse`, `right_inverse`; `ambient_unit` only removes the pure-power disjunct |
| `ReturnFamily.pairGenerator_isMortal_iff_returnFamily` | MM-C05 seam | one transition, one cut | `ambient_powers_ne_zero`, absorbed by the disjunct |
| `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero` | R32-S02 | no transitions | `left_inverse`, `right_inverse` |

The parabolic bridge grammar (`ParabolicBlade.exceptionalChain_eq_zero_iff`, M4-M03) is the same
algebra applied to a cut carried by the derived word `S²` rather than by a generator; its
fixed-chain equivalence genuinely needs `ρ ≠ 0`, because it compares one chain with one bridge
word instead of mortality with a loop-closed path.

Registry consequences already applied: `D2-S01` (the `M₂(3)` projective hard core) was
`audited` with a pending "formalize the minimal-word case split"; the case split is
unnecessary, because `mortal_adjoin_outer_iff` at two generators of dimension two *is* the
reduction, and the several-endpoint form is `isMortal_rankOne_iff`. Its evidence is now
"formalized reduction; audited census". `R32-O01` cited `ReturnFamily.wordProduct_unitSquare_eq_zero_iff`;
that lemma now lives in `MatrixSemigroup.lean` with `Nontrivial + NoZeroDivisors` instead of a
field. `FORMALIZATION.md` cited a declaration `unitFamily_mortal_boundaryOuter_iff` that does not
exist; the declaration is `mortal_boundaryOuter_iff`.

Not yet done, and cheap: re-derive the four subsumed theorems from the hub and delete their
split hypotheses and the duplicated fracture arguments. Nothing downstream uses the split
hypotheses except to discharge them.

For the DAG: this is the "independently reusable" node Sol's admission rule asks for. The
proposed nodes *rank-one separator*, *singular-return compression*, *split-return normal form*,
and *two-plane edge square* are its specializations; the *three-mode valuation guard* and the
*3+3+2+1 realization* are constructions whose correctness theorems are its one-transition case.
One Reduction node, `mm/interface-compression`, with those as children.

## 2. Rank census for every open cell

Interface compression turns each open cell into finitely many bridge-path problems indexed by
the ranks of its singular generators, over the free monoid of the remaining generators. The
census below is a corollary of §1 and of `not_isMortal_of_forall_isUnit`; only the decidability
verdicts import external theorems (Bacik, order-four Skolem).

**`M₂(k)`.** Rank profile (2,…,2) is immortal; a zero generator is mortal; `m` rank-one
generators and `k−m` units give projective incidence on `P¹(ℚ)` between `m` source points and
`m` target lines under `k−m` Möbius maps. With at most one unit this is order-two Skolem and
decidable. So `[Q M₂(k)]` is one node, *projective incidence with `n` Möbius maps*, `n = k−1`
in the hard profile; `M₂(3)` is `n = 2`.

**`M₃(2)`.** Already censused (`R32-O01`, `R32-S01`, `R32-S02`): rank-one profiles are order-three
Skolem; `(2,2)` is `GPI₂`; `(3,2)` is the three-mode unary return family.

**`M₃(3)`.** Not a frontier target, but the strongest untried lever below `M₃(2)`: by CHHN
Theorem 4 with `(d,h,k) = (3,1,2)`, `M₃(3) ≤ M₆(2)`, so an undecidability proof closes
`M₃(3), M₃(4), M₄(3), M₅(3), M₆(2), M₇(2), M₈(2)`. Its profiles:

| Profile | Bridge problem |
| --- | --- |
| `(3,3,1)` | `Z₃(2)` restricted to unit generators: `∃ w ∈ {A,B}*, r A_w c = 0` |
| `(3,3,2)` | a two-dimensional return family `{O A_w U : w ∈ {A,B}*}` realized in dimension three |
| `(3,2,2)` | two-vertex graph with `2×2` edges `O_i Aⁿ U_j` (unary, three modes) |
| `(3,2,1)`, `(3,1,1)` | scalar edges through one rank-two vertex; `(3,1,1)` is order-three Skolem |
| `(2,2,2)` | three planes in `ℚ³`, pairwise sharing a line: a compatible three-vertex edge graph |

`(3,3,1)` shows `Z₃(2)` over units is `M₃(3)`-hard; the paired `M₃(4)` route is the same shape
with three transitions.

**`M₄(2)`.** Not discussed anywhere in the corpus, although it closes the same seven cells as
`M₃(3)` (`M₄(2) ≤ M₄(3), M₅(2), M₅(3), M₆(2), M₇(2), M₈(2)`). Its profiles:

| Profile | Verdict or bridge problem |
| --- | --- |
| `(4,4)` | immortal |
| `(4,1)`, `(3,1)`, `(2,1)`, `(1,1)` | order-at-most-four Skolem: **decidable** by Bacik 2025; a new decidable stratum |
| `(2,2)` | two-vertex graph with four arbitrary `2×2` edges; one singular loop edge and three units is exactly the `M₂(3)` hard core (CHHN `M₂(3) ≤ M₄(2)`); a singular cross edge gives the two-parameter equation `r Zᵃ W Xᵇ c = 0`; two singular edges are finite |
| `(4,2)` | four-mode unary return family `{V Aⁿ U} ⊂ M₂(ℚ)`, `A ∈ GL₄` |
| `(4,3)` | four-mode unary return family in `M₃(ℚ)` |
| `(3,3)` | two rank-three generators: `3×3` edge square with compatibility on a shared plane |
| `(3,2)` | rectangular edge square with one `3×3`, one `2×2`, and two off-diagonal edges |

The `(4,2)` artery inherits every `ReturnFamily`/`ReturnGuard` declaration unchanged, because
those are dimension-generic (`ambient : Square Large R`). The `M₃(2)` guard uses modes
`(p⁻¹, 1, p^{d−1})`; a fourth mode is available here. Whether it escapes `R32-O06` (rail
rigidity) and `R32-O18` (finite carry-mode atlases are eventually periodic) is unexamined: both
records are stated for the three-mode chart, and the state space is still one projective point,
so the fourth mode enlarges the alphabet, not the register. This is a direction, not a result.

**`M₄(3)`.** `(4,4,1)` is `Z₄(2)` over units; the overlap-queue compiler `M4-C01`/`M4-C02` is the
rank-one instance with singular data allowed; the parabolic blade is the rank-two-cut instance
(its cut is the word `S²`, not a generator). `(4,4,2)` and `(4,4,3)`, two- and three-dimensional
return families over a binary free monoid realized in dimension four, have no record.

**`M₅(3)`.** Route 1 of the frontier (five-state two-letter scalar series plus separator) is the
`(5,5,1)` profile. `(5,5,2)`, `(5,5,3)`, `(5,5,4)`, return families of dimension two, three, and
four over a binary free monoid realized in five dimensions, are unlisted routes; the decimal
setter's delimiter (rank three, square of rank two, cube of rank one) is a `(5,5,3)` instance
whose parser (`MM-S74`) re-derives the bridge factorization by hand.

**`M₅(2)`, `M₆(2)`, `M₇(2)`, `M₈(2)`.** See §3: their rank-one profiles are open Skolem
instances, so no census can be completed on the decidable side.

## 3. The Skolem wall

`Z_d(1)` is the order-`d` Skolem problem. Through `rankOnePair_isMortal_iff` (or §1),
`M_d(2)` restricted to one unit and one rank-one generator is exactly `∃ n, O Aⁿ U = 0`, and
every order-`d` rational linear recurrence is `O Aⁿ U` for a companion `A`. Hence

```text
M_d(2)^{(d,1)} ≡ Skolem(d),   Z_d(k) ⊇ Skolem(d),   M_d(k) ⊇ Skolem(d)   (k ≥ 2).
```

Skolem is decidable unconditionally through order four (Bacik, already in `references/`) and
open from order five. Consequently:

- no decidability proof exists today for any of `M₅(2)`, `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)`,
  `Z₅(2)`; a proof would settle order-five Skolem. These cells are attackable only from the
  undecidability side, which the frontier does without stating the reason;
- for `d ≤ 4` (`M₂(k)`, `M₃(k)`, `M₄(k)`) there is no Skolem obstruction, so decidability
  remains a live outcome, consistent with the frontier's `M₂(3)` prior.

This is classical (mortality with a rank-one generator is Skolem), but it appears nowhere in the
corpus; it belongs in the DAG as an Obstruction node with `Origin = Literature` attached to all
`d ≥ 5` frontier cells, and it should be cited in the mortality-table page's remarks. The
reduction half is formalizable now; the companion-matrix embedding is a few lines.

## 4. The structured scalar problem is affine reachability

In `Z̊_d(k)` every generator fixes `e₁` as a column (`pairedGenerator_mulVec_anchor`,
`nearyScalarZero62_fixes_anchor`). Writing `A = [[1, ρᵀ],[0, A']]`, the row action is

```text
(y₁, y') A = (y₁, y₁ρᵀ + y'A'),
```

so a boundary row with `λ₁ ≠ 0` moves as an affine point of `ℚ^{d−1}` under the maps
`y' ↦ y'A' + λ₁ρᵀ`, and `λ A_w γ = 0` says the point lands on the affine hyperplane
`⟨y', γ'⟩ = −λ₁γ₁`. With `λ₁ = 0` the problem is `Z_{d−1}(k)` for the linear parts.

```text
Z̊_d(k) ≡ point-to-hyperplane reachability for k affine maps of ℚ^{d−1}.
```

Consequences: `Z̊₆(2)` states that point-to-hyperplane reachability for **two rational affine
maps of `ℚ⁵`** is undecidable, a corollary the binary-compiler page does not state; CHHN
Theorem 7 (`Z̊_d(hk+1) ≤ Z_{1+k(d−1)}(h+1)`) is the stacking of `k` affine spaces on one shared
constant coordinate; and the `M₂(3)` affine residue `F(z)=az, G(z)=bz+1` is the `d = 2`
instance, which links the `D2` campaign to the `Z` table. This is a Definition node, not a
theorem, and it costs one paragraph.

## 5. The CHHN generator–dimension trade is a prefix transducer

`FORMALIZATION.md` records that "CHHN's generator–dimension and scalar-to-corner frontier
transports remain external paper". The table's `M₆(3)`, `M₁₂(2)`, and the conditional edges
`M₄(3) ⇒ M₈(2)`, `M₃(4) ⇒ M₉(2)`, `M₃(3) ⇒ M₆(2)`, `M₂(3) ⇒ M₄(2)` all rest on CHHN Theorem 4,
`M_d(hk+1) ≤ M_{kd}(h+1)`.

The corpus already contains the general mechanism: `WeightedTransducer.generator` realizes any
deterministic matrix transducer with `s` states and outputs in `M_d` as `s·d`-dimensional
generators, one per input letter, and `prefixMachine_mortal_iff_normalized` proves the mortality
equivalence for the four-state binary code `0,100,101,110,111` using the synchronizing word `00`.
A complete prefix code with `k` internal nodes over `h+1` letters has `hk+1` leaves; the
root-plus-chains codes CHHN packs always have a synchronizing word. Generalizing
`PrefixMortality` from the fixed four-state code to an arbitrary complete prefix code with a
synchronizing word therefore formalizes Theorem 4 in full, makes `M₆(3)` and `M₁₂(2)` formal
transport edges, and exhibits `M₁₀(2)` as that packing followed by common-image restriction
(`MM-C02`). Estimated size: one module of the same shape as `PrefixMortality.lean`.

## 6. The reward lattice

The frontier ranks cells by tractability. The table records which open cells each candidate
theorem would close, by padding, generator monotonicity, and Theorem 4.

| Undecidability of | Closes | Count |
| --- | --- | ---: |
| `M₂(3)` | `M₂(k≥3)`, `M₃(3)`, `M₃(4)`, `M₄(2)`, `M₄(3)`, `M₅(2)`, `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)`; not `M₃(2)` | 13 |
| `M₃(2)` | `M₃(3)`, `M₃(4)`, `M₄(2)`, `M₄(3)`, `M₅(2)`, `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)`; not `M₂(k)` | 10 |
| `M₃(3)` | `M₃(4)`, `M₄(3)`, `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)` | 7 |
| `M₄(2)` | `M₄(3)`, `M₅(2)`, `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)` | 7 |
| `M₂(4)` | `M₂(k≥4)`, `M₆(2)`, `M₇(2)`, `M₈(2)` | 6 |
| `M₅(2)` | `M₅(3)`, `M₆(2)`, `M₇(2)`, `M₈(2)` | 5 |
| `M₄(3)` | `M₅(3)`, `M₈(2)` | 3 |
| `M₂(5)` | `M₂(k≥5)`, `M₈(2)` | 3 |
| `M₃(4)`, `M₅(3)`, `M₈(2)` | themselves | 1 |

`M₂(3)` and `M₃(2)` are incomparable. `M₃(3)` and `M₄(2)` are the only untargeted cells with
reward seven, and `M₂(5)`, projective incidence with four Möbius maps, would already close
`M₈(2)`. The DAG's mortality-table view should be computed from exactly these edges; the
Z-table and R-table are the same computation from `Z̊_d(k) ≤ M_d(k+1)`, `Z_d(k) ≤ R_{d+1}(k)`,
and `R_d(k) ≤ Z_d(k)`.

## 7. Corrections to the proposed DAG

- `[R rank-one separator]`, `[R singular return]`, and the edge-square nodes become children of
  `mm/interface-compression`; `[C three-mode valuation guard]` and `[C 3+3+2+1 realization]`
  keep their construction identity, and their mortality theorems point at the hub.
- `[Q M₂(k)]` is one node parametrized by the number of Möbius maps; `M₂(3)` is not the only
  entry with a transport edge (`M₂(4) ≤ M₆(2)`, `M₂(5) ≤ M₈(2)`).
- Add `[O Skolem wall]` (Literature, Reported) with `attacks` edges to every `d ≥ 5` frontier
  cell, and record on the table that those cells have no decidable outcome available.
- Add `[D affine hyperplane reachability]` as the canonical meaning of `Z̊`, with the corollary
  for two affine maps of `ℚ⁵` as a consequence of `Z₆(2)`.
- Replace the literature transport edges by `[R prefix-transducer packing]` once §5 is
  formalized; until then they carry `Origin = Literature, Assurance = Reported`.
- Add frontier nodes for `M₃(3)`, `M₄(2)`, and `M₅(2)` with their census children; the
  `M₃(2)` return-family machinery is shared with `M₄(2)^{(4,2)}` by dimension genericity.

## 8. Verification state and caveats

- `InterfaceCompression.lean`, the modified `MatrixSemigroup.lean`, and `ReturnFamily.lean` build;
  `#lint- in MatrixMortality.InterfaceCompression` is silent. The two new theorems are listed in
  `AxiomAudit.lean`; `verification/axioms.txt` must be regenerated after the full rebuild, which
  the change to the foundations module forces.
- Sections 2–6 are consequences of existing declarations plus CHHN Theorem 4 and Bacik; none is
  a new Lean theorem yet. The `(2,2)` analysis of `M₄(2)` and the cross-edge case are hand
  derivations.
- The frontier-specific modules (roughly 330 files) were not re-read; their contents entered
  through `SALVAGE.md`, `FRONTIER.md`, and the principal-declaration map, so a connection that
  lives only inside one of those proofs may have been missed.
