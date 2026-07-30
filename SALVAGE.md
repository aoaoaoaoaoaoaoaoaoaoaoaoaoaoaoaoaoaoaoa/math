# Salvage Theorem Registry

This file is the canonical index of reusable results obtained while an attack failed to settle
its target. `FRONTIER.md` owns strategy; `FORMALIZATION.md` owns Lean coverage; `audits/` own
bounded reviews. Raw prompts and undigested Pro reports are not repository artifacts.

## Record Contract

Every record has a stable identifier and five core fields:

- **kind**: compiler, obstruction, structure theorem, decidable stratum, certificate, or partial
  mechanism;
- **evidence**: `reported`, `audited`, `formalized`, or `computational`;
- **disposition**: `stock`, `active`, `closed`, `parked`, or `graduated`;
- **scope**: the exact hypotheses and conclusions that may be reused;
- **use**: the attack or proof obligation for which the result is operational;

Every active record also states the next promotion step. A graduated record instead cites its
formal artifact.

The first namespace component identifies the campaign: `MM` for general matrix-mortality
compilers, `R32` for the rank-three binary frontier `M₃(2)`, `M4` for the `M₄(3)` frontier,
`G3` for the three-letter GPCP and `M₃(4)` frontier, and `D2` for the dimension-two wall.
The second component identifies the result class: `C` compiler, `O` obstruction, `M` partial
mechanism, `S` structure theorem, or `D` decidable stratum. Numbers never change after
assignment.

`reported` means that the result survives only as a contracted statement from an external
review. It cannot support a publication claim. `audited` means that its proof has been checked
independently in this project. `formalized` means that the cited Lean declaration passes the
strict gate. `computational` never licenses an unbounded theorem.

`stock` is ready for reuse without scheduled promotion. `active` has a live use or promotion
task. `parked` remains valid but lacks a current route to its target. `graduated` has entered the
formal corpus. `closed` is retained only as a warning after refutation or strict subsumption.

Agents should cite record identifiers in research prompts and frontier updates. A prompt must
carry the record's scope, not merely its conclusion. A reusable result without enough statement
or construction to recover its use does not belong here. GitHub issues own scheduled work; this
file owns the mathematical stock.

## Index

| ID | Kind | Result | Evidence | Disposition |
| --- | --- | --- | --- | --- |
| [`MM-C01`](#mm-c01-fixed-anchor-rank-one-compiler) | compiler | common-fixed-column scalar zero to mortality | formalized | graduated |
| [`MM-C02`](#mm-c02-common-image-restriction) | compiler | mortality-preserving restriction to a common image | formalized | graduated |
| [`MM-C03`](#mm-c03-scheduled-binary-compiler) | compiler | fixed-width tag strokes to a total two-letter scalar series | formalized | graduated |
| [`MM-C04`](#mm-c04-internal-word-sandwich-minimization) | compiler | internal low-rank words repair reachable/observable minimization | formalized | graduated |
| [`MM-O01`](#mm-o01-all-placement-packing-rank) | obstruction | literal CHHN packing has exact rank six for every separator placement | formalized | graduated |
| [`MM-O02`](#mm-o02-one-sided-phase-overlap) | obstruction | standard common-line phase fusion becomes one-sided | reported | parked |
| [`MM-O03`](#mm-o03-two-channel-boundary-tax) | obstruction | exact diagonal rank-two punctuation costs two states beyond Hankel rank | formalized | graduated |
| [`MM-O04`](#mm-o04-uniform-rank-four-paired-series) | certificate | the paired scalar series has exact Hankel rank four | formalized | graduated |
| [`MM-O05`](#mm-o05-width-three-scheduled-rank) | obstruction | the width-three scheduled series has exact rank five | formalized | graduated |
| [`MM-O06`](#mm-o06-pure-power-punctuation-obstruction) | obstruction | an exact isolated toggle cannot also punctuate through a pure power | audited | stock |
| [`MM-O07`](#mm-o07-setter-parameter-rigidity) | obstruction | source-boundary alignment fixes the setter parameter | audited | stock |
| [`MM-O08`](#mm-o08-full-algebra-prefix-pair) | obstruction | the exact ten-state prefix pair spans the full matrix algebra | formalized | graduated |
| [`MM-O09`](#mm-o09-two-state-ternary-prefix-image) | obstruction | a literal two-state ternary decoder has no five-state common-image restriction | audited | stock |
| [`MM-O10`](#mm-o10-additive-toggle-fusion-cycle) | obstruction | the normalized toggle-minus-separator ansatz has rank three at every power | audited | stock |
| [`MM-O11`](#mm-o11-full-algebra-paired-binary-family) | obstruction | the paired-binary mortality family spans the full six-state algebra | formalized | graduated |
| [`MM-M01`](#mm-m01-off-diagonal-companion-interface) | partial mechanism | off-diagonal rank-two bridge has a complete fracture grammar | audited | stock |
| [`MM-M02`](#mm-m02-bordered-toggle) | partial mechanism | one lifted toggle has a stable rank-two third power | audited | parked |
| [`MM-M03`](#mm-m03-five-state-setter-punctuation) | partial mechanism | a mixed delimiter word is an exact internal rank-one separator | audited | active |
| [`MM-M04`](#mm-m04-swapped-digit-setter) | partial mechanism | reversing the nonzero ternary digits preserves the setter and makes every transfer orientation preserving | audited | active |
| [`MM-S01`](#mm-s01-square-run-projective-normal-form) | structure theorem | malformed square runs reduce to rational projective pole avoidance | audited | active |
| [`MM-S02`](#mm-s02-reset-zero-projective-peeling) | structure theorem | the ordinary reset cannot reach a false pole after one transfer | audited | active |
| [`MM-S03`](#mm-s03-centered-setter-carry) | structure theorem | setter orbits obey an integer valuation-and-suffix carry recurrence | audited | active |
| [`MM-S04`](#mm-s04-reverse-suffix-discrepancy) | structure theorem | setter resonance is a word-valued discrepancy queue with a bounded front fringe | audited | active |
| [`MM-S05`](#mm-s05-distinguished-boundary-beta-shell) | obstruction | the distinguished-boundary `β`-shell cannot reach a false pole | audited | active |
| [`MM-S06`](#mm-s06-valuation-one-divisor-normal-form) | structure theorem | every integral valuation-one pole lies on a finite family of divisor rays | audited | active |
| [`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction) | structure theorem | the swapped setter reduces integral valuation-one poles to finitely many primitive slopes | audited | active |
| [`MM-S08`](#mm-s08-swapped-distinguished-boundary-beta-shell) | obstruction | the swapped distinguished boundary cannot reach either single-erasure pole | audited | active |
| [`MM-S09`](#mm-s09-canonical-swapped-residue-cannot-hit-a-pole) | obstruction | the unavoidable all-erasure residue cannot meet a valuation-one pole at emitted widths | audited | active |
| [`MM-S10`](#mm-s10-swapped-target-suffix-sieve) | structure theorem | pole compatibility fixes `β+2` lower digits and excludes the residue `Δ=ρ−1` | audited | active |
| [`R32-S01`](#r32-s01-split-return-normal-form) | structure theorem | rank-two cuts reduce one-unit binary mortality to a `2 × 2` return recurrence | formalized | graduated |
| [`R32-S02`](#r32-s02-two-plane-edge-square) | structure theorem | two rank-two generators are a two-vertex square of `2 × 2` edges | formalized | graduated |
| [`R32-O01`](#r32-o01-rank-one-profile-collapse) | obstruction | a rank-one generator reduces mortality to order-at-most-three scalar recurrence zeros | audited | stock |
| [`R32-S03`](#r32-s03-returnsquare-normal-form) | structure theorem | ReturnSquare mortality is an exact scalar bridge over positive returns | formalized | active |
| [`R32-O02`](#r32-o02-two-return-square-cage) | obstruction | no two positive ReturnSquare returns can vanish | formalized | graduated |
| [`R32-O03`](#r32-o03-reversible-stack-state-tax) | obstruction | literal reversible binary-stack returns require at least four exact states | formalized | graduated |
| [`R32-O04`](#r32-o04-quadratic-pencil-verification-collapse) | obstruction | three simple modes cannot reversibly verify squaring | formalized | graduated |
| [`R32-O05`](#r32-o05-jordan-parity-verifier-collapse) | obstruction | the rank-compatible parity-Jordan verifier is unique and immortal modulo seven | formalized | graduated |
| [`R32-D01`](#r32-d01-returnsquare-immortality-walls) | decidable stratum | nonnegative parameters and a uniform outer negative half-line are immortal | formalized | stock |
| [`R32-D02`](#r32-d02-prime-power-returnsquare-classification) | decidable stratum | prime-power ReturnSquare is mortal exactly at one-return resonances | formalized | graduated |
| [`R32-M01`](#r32-m01-generic-reverse-edge-compiler) | partial mechanism | projective incidence generically embeds into a compatible two-plane edge square | formalized | active |
| [`R32-M02`](#r32-m02-finite-quotient-sieve) | partial mechanism | finite monoid quotients give complete modular no-certificates for fixed candidates | formalized | active |
| [`R32-M03`](#r32-m03-two-scale-return-conversion) | partial mechanism | a minimal two-scale return pencil has nonresonant multi-return zeros | formalized | active |
| [`R32-M04`](#r32-m04-amalgamated-valuation-guard) | partial mechanism | one three-mode return family combines punctuation, wait verification, and a permanent trap | formalized | active |
| [`R32-S04`](#r32-s04-guarded-return-normal-form) | structure theorem | physical mortality is deterministic reachability for the ready-tail recurrence | formalized | active |
| [`R32-S05`](#r32-s05-prefix-shift-and-affine-residual) | structure theorem | each legal step decodes one p-adic prefix and updates the reciprocal residual affinely | formalized | active |
| [`R32-S06`](#r32-s06-resonance-localization) | structure theorem | every nonresonant continuation descends and every infinite ready chain resonates arbitrarily late | formalized | active |
| [`R32-O06`](#r32-o06-rational-affine-wait-rail-rigidity) | obstruction | no reduced rational chart supports a nontrivial affine wait rail at infinitely many prime powers | formalized | graduated |
| [`R32-S07`](#r32-s07-decoded-residual-address-normal-form) | structure theorem | mortality is finite inverse-address membership in disjoint rational p-adic branch spheres | formalized | active |
| [`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve) | partial mechanism | every primitive reduction either resets modulo a cyclotomic prime or swallows it in the common cancellation | formalized | active |
| [`R32-S08`](#r32-s08-terminal-defect-cocycle) | structure theorem | terminal-defect coordinates expose a second-order denominator recurrence and separate fixed from novel cancellation | formalized | active |
| [`R32-S09`](#r32-s09-complete-cancellation-law) | structure theorem | every base-coprime cancellation depth is the minimum of the terminal-defect and displacement depths | formalized | active |
| [`R32-S10`](#r32-s10-logarithmic-wait-and-height-envelope) | structure theorem | legal waits are logarithmic in primitive height and every reduced step is uniformly height-Lipschitz | formalized | active |
| [`R32-S11`](#r32-s11-primitive-factor-terminal-gate) | structure theorem | a large primitive cyclotomic radical forces terminality or a surviving finite-quotient reset | formalized | active |
| [`R32-S12`](#r32-s12-exact-order-projective-automata) | structure theorem | primitive divisors induce finite projective automata with exact swallowed-factor semantics | formalized | active |
| [`R32-S13`](#r32-s13-canonical-decoded-integral-lift) | structure theorem | every decoded rational path lifts canonically to primitive integral execution | formalized | active |
| [`R32-S14`](#r32-s14-drift-divisor-certificate-classification) | decidable stratum | drift-divisor certificates are exactly finite cyclic-orbit avoidance | formalized | active |
| [`R32-S15`](#r32-s15-finite-quotient-completeness) | obstruction | terminal exclusion is cancellation exclusion; synchronized prime products cannot amplify certificates | formalized | active |
| [`R32-S16`](#r32-s16-cancellation-blow-up-and-unbounded-depth) | obstruction | primitive cancellation is a surjective projective blow-up with no uniform finite-jet bound | formalized | active |
| [`R32-S17`](#r32-s17-normalized-tangent-cocycle) | structure theorem | consecutive primitive reductions form a recursive two-dimensional tangent cocycle with exact cyclotomic support | formalized | active |
| [`R32-S18`](#r32-s18-fixed-support-localization-obstruction) | obstruction | fixed-support localization isolates the cyclotomic determinant but retains an infinite strict tower of novel cancellation depths | formalized | active |
| [`R32-S19`](#r32-s19-canonical-cyclotomic-collision-ladders) | structure theorem and obstruction | tangent content is exactly multiplicative, yet one canonical reset orbit can swallow four successive novel cyclotomic factors | formalized | active |
| [`R32-S26`](#r32-s26-evaluation-frame-gauge-closure) | structure theorem and closure | the parameter-jet transition is an exact frame coboundary, and deep frame defect localizes to the reset shell | formalized | graduated |
| [`R32-S27`](#r32-s27-rational-gap-macro-pumping) | structure theorem and obstruction | exact branch similarity and rational height separation bound every noncyclic repetition of one fixed macro | formalized | active |
| [`M4-C01`](#m4-c01-two-state-pushout-compiler) | compiler | binary deterministic two-state scalar control compiles to three `4 × 4` matrices | formalized | graduated |
| [`M4-O01`](#m4-o01-exact-toggle-fusion-leaves-an-immortal-core) | obstruction | exact local toggle fusion preserves a nonzero common anchor | formalized | graduated |
| [`M4-O02`](#m4-o02-two-private-state-phase-signature) | obstruction | two private quotient states cannot isolate one exceptional cyclic phase | formalized | graduated |
| [`M4-S01`](#m4-s01-odd-phase-macro-cut) | structure theorem | paired Neary roles inherit a rigid macro-stroke language | reported | active |
| [`M4-O03`](#m4-o03-closed-serialization-collapse) | obstruction | finite closed-token queue serialization is decidable | formalized | graduated |
| [`M4-O04`](#m4-o04-exact-internal-final-code-defect) | obstruction | distinct exact binary codes for one macro force commuting upper images | formalized | graduated |
| [`M4-O05`](#m4-o05-direct-two-state-first-return-recoding) | obstruction | the present four Neary roles have no direct two-state first-return code | reported | active |
| [`M4-M01`](#m4-m01-mixed-cube-root-punctuation) | partial mechanism | rational cube-root toggles reduce mixed punctuation to incidence equations | audited | parked |
| [`G3-O01`](#g3-o01-four-role-macro-irreducibility) | obstruction | exact nonerasing macros cannot reduce the four source roles to three letters | formalized | graduated |
| [`G3-S01`](#g3-s01-shift-equivariant-zero-incidence) | structure theorem | same-zero state dimension is equivariant projective incidence dimension | audited | active |
| [`G3-M01`](#g3-m01-free-group-discrepancy-engine) | partial mechanism | free cancellation implements queue deletion with an all-path converse | reported | active |
| [`D2-S01`](#d2-s01-projective-hard-core) | structure theorem | `M₂(3)` is equivalent to two-generator projective incidence | audited | active |
| [`D2-S02`](#d2-s02-monotone-affine-path-form) | structure theorem | normalized affine words form monotone exponent paths | audited | stock |
| [`D2-D01`](#d2-d01-projectively-unimodular-stratum) | decidable stratum | projectively unimodular hard-core instances are decidable | audited | stock |
| [`D2-D02`](#d2-d02-invariant-pair-stratum) | decidable stratum | invariant projective pairs reduce to abelian-by-`C₂` reachability | reported | active |
| [`D2-D03`](#d2-d03-common-multiplier-stratum) | decidable stratum | rational affine maps with one multiplier are decidable under regular control | reported | active |
| [`D2-D04`](#d2-d04-single-base-affine-stratum) | decidable stratum | rational-subset incidence in `G_q^±` is decidable | reported | active |
| [`D2-D05`](#d2-d05-prescribed-translation-count) | decidable stratum | prescribed translated-letter count is decidable by rational-base carries | audited | stock |
| [`D2-D06`](#d2-d06-private-prime-peeling) | decidable stratum | a private multiplier prime decides every noncritical endpoint shell | audited | stock |
| [`D2-D07`](#d2-d07-bounded-valuation-orthants) | decidable stratum | bounded cooriented affine families have finite successful state spaces | audited | stock |
| [`D2-M01`](#d2-m01-benchmark-critical-shell) | partial mechanism | the mixed-prime benchmark reduces generically to one guarded `5`-adic shell | audited | active |

## Matrix Mortality

### MM-C01: Fixed-anchor rank-one compiler

**Kind:** compiler  
**Evidence:** formalized
**Disposition:** graduated

Let every active matrix `X_a` fix a nonzero column `e`, let `Le ≠ 0`, and put `P = CL`. Then the
family `{X_a} ∪ {P}` is mortal exactly when `LX_wC = 0` for some active word `w`. The converse
fractures every arbitrary product at every occurrence of `P`; the fixed column replaces
invertibility at the exterior row.

**Scope:** empty internal blocks are harmless only when `LC ≠ 0`; the theorem does not make the
scalar source undecidable.

**Artifact:** `MatrixMortality.fixedAnchor_mortal_adjoin_outer_iff` in
[`TerminalTile.lean`](MatrixMortality/TerminalTile.lean).

**Use:** prefer this theorem to a bespoke separator argument whenever a common fixed column is
available.

### MM-C02: Common-image restriction

**Kind:** compiler  
**Evidence:** formalized
**Disposition:** graduated

Suppose every generator maps the ambient space into a common subspace `K`, and explicit integral
maps `J : K → V` and `Q : V → K` satisfy `QJ = I` and `A_iJ = JB_i`. Mortality of the restricted
family follows from mortality upstairs. Conversely, if `B_w = 0`, then `A_w` kills `K`; appending
any generator whose image lies in `K` gives a zero ambient product.

**Scope:** the appended-letter converse is required. Restriction alone may introduce zero
products absent from the ambient family.

**Artifact:** `MatrixMortality.isMortal_commonImage_iff` and
`MatrixMortality.restrictedPrefixGenerator_mortal_iff_prefixMachine` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean) and
[`PrefixMortality.lean`](MatrixMortality/PrefixMortality.lean).

**Use:** this is the reusable core of the `12 → 10` binary mortality compiler.

### MM-C03: Scheduled binary compiler

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

A deletion-width-`β` tag stroke consists of one rule role followed by `β−1`
erasures. After reversal its phase schedule is fixed. Two generators can therefore
select only the tag letter while a cyclic `β`-phase lower channel selects rule or
erasure semantics. The representation has coordinates

```text
(affine, upper, lower₀, …, lower_{β−1})
```

and dimension `β+2`.

The decoder is total on the binary free monoid and preserves the source
coefficient exactly. Every lawful tile history has an explicit reverse-stroke
encoding. Conversely, a zero coefficient invokes the terminal-match normal form,
so the decoded roles form complete strokes; in particular, every zero word has
length divisible by `β`. Unfinished clock cycles cannot create zeros.

**Scope:** this is a fixed-width compiler, not a fixed-dimensional reduction from
the present undecidable source. Neary's universality compiler sets `β=10·period`.

**Artifact:** `MatrixMortality.scheduledCoefficient_eq_sideCoefficient`,
`MatrixMortality.decodeScheduled_historyCode`,
`MatrixMortality.scheduledCoefficient_zero_length_dvd`, and
`MatrixMortality.scheduledBinary_zero_iff_tagHaltsFrom` in
[`ScheduledBinary.lean`](MatrixMortality/ScheduledBinary.lean).

**Use:** any future undecidable source at constant deletion width `β` immediately
gives a two-generator scalar representation in dimension `β+2`. At `β=3`, the
conditional rewards are `Z₅(2)`, `M₅(3)`, and `R₆(2)`.

### MM-C04: Internal-word sandwich minimization

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

Let `A : Σ → M_d(K)` and suppose a nonempty physical word `ω` has nonzero product

```text
E=A_ω=UW,
```

where `U : K^r → K^d` and `W : K^d → K^r` both have rank `r`. Define

```text
R=span{A_w im U : w∈Σ*},
N={x∈R : WA_wx=0 for every w∈Σ*},
H=R/N.
```

Both `R` and `N` are invariant. Let `B_a` be the action induced on `H`. Then

```text
{A_a} is mortal  ⇔  {B_a} is mortal.
```

The forward implication passes a zero product to every invariant subquotient. Conversely, if
`B_z=0`, then `A_zR⊆N`, so `WA_zU=0` and the entirely physical repair word satisfies

```text
A_{ωzω}=EA_zE=U(WA_zU)W=0.
```

No syntax or exterior nonvanishing hypothesis is required. Moreover,

```text
dim H = rank [WA_{uv}U]_{u,v∈Σ*},
```

the flattened block-Hankel rank of the matrix-valued series `F(w)=WA_wU`. The quotient is its
minimal exact linear realization.

**Scope:** the result is exact-linear. It does not preserve only the zero set, and it does not
lower dimension unless the sandwich series has smaller block-Hankel rank. If `H=0`, an
ambient mortal word already exists. Independent nonzero generator scaling preserves mortality,
which supplies the algebraic denominator-clearing step. Extracting a chosen rational basis and
concrete quotient matrices is not part of the generic theorem.

**Use:** search a known-safe mortality family for an internal low-rank word, minimize its
matrix-valued sandwich, and inherit a complete arbitrary-word converse without adding a
generator. For `M₅(3)`, compute rank-two sandwich realizations inside the established
six-state, three-generator families before designing another five-state parser.

**Artifact:** `MatrixMortality.InternalSandwich.mortal_quotient_iff`,
`MatrixMortality.InternalSandwich.ambient_mortal_of_quotient_subsingleton`,
`MatrixMortality.InternalSandwich.range_reachableBehavior_eq_span`,
`MatrixMortality.InternalSandwich.quotient_finrank_eq_blockHankel`, and
`MatrixMortality.InternalSandwich.quotient_finrank_le_of_represents` in
[`InternalSandwich.lean`](MatrixMortality/InternalSandwich.lean). The common exact-behavior
primitive is in [`ExactBehavior.lean`](MatrixMortality/ExactBehavior.lean); full generated
matrix algebras force ambient sandwich dimension through
`quotient_finrank_eq_card_of_wordProductSpan_eq_top` in
[`FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean). Independent nonzero
generator scaling is `MatrixMortality.isMortal_smulMatrix_iff` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean). The independent reconstruction
and edge-case audit are in
[`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md).

### MM-O01: All-placement packing rank

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For every placement of the four ordinary `3 × 3` payloads and the rank-one separator in the
literal three-generator `6 × 6` CHHN packing, the selected scalar coefficient series has exact
linear-representation dimension six. A placement-dependent six-prefix family and a
semantically selected six-suffix family expose a nonsingular finite Hankel section.

**Scope:** this excludes exact five-state realizations of that coefficient series. It does not
exclude a different five-state series with the same zero set.

**Use:** reject further exact minimization of the literal CHHN packing and require a changed
coefficient series or punctuation architecture.

**Artifact:** `chhnNeary_exactRepresentation_six_le_card` in
[`MatrixMortality/CHHNPackingRank.lean`](MatrixMortality/CHHNPackingRank.lean), built on the
generic kernels in [`MatrixMortality/CHHNPacking.lean`](MatrixMortality/CHHNPacking.lean).
The reconstruction and independent 120-placement executable check are documented in
[`audits/chhn-all-placement-rank-2026-07-26.md`](audits/chhn-all-placement-rank-2026-07-26.md).

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O02: One-sided phase overlap

**Kind:** obstruction  
**Evidence:** reported  
**Disposition:** parked

In the standard two-slot selector architecture, a common invariant line reportedly forces its
overlap vector into either the upper-word or lower-word invariant plane. The resulting bridge
depends on only one positional-value channel; after this forcing step, its zero language is
effectively regular.

**Scope:** the forcing statement concerns the stated common-line phase fusion, including its
projective rescalings. The regularity conclusion is conditional on the global mortality
converse reducing malformed words to finitely many such bridges. It is not a general
impossibility theorem for five-state zero-set representations.

**Use:** reject a proposed common-line selector only after matching all of its hypotheses.

**Artifact:** bibliographic scope is recorded in
[`audits/m44-prior-art-2026-07-22.md`](audits/m44-prior-art-2026-07-22.md#8-the-phase-fusion-obstruction-and-regular-positional-value-languages).

**Next:** recover and audit the forcing proof before using it to reject another architecture.

### MM-O03: Two-channel boundary tax

**Kind:** obstruction

**Evidence:** formalized

**Disposition:** graduated

Let `A : Σ* → Mₙ(K)`, let `U=[u₀ u₁]` and `V=[v₀;v₁]` both have rank two, and suppose

```text
V A_w U = [[0,0],[0,h(w)]]
```

for every word `w`. If `h` has Hankel rank `d`, then `n ≥ d+2`.

Write `R = span{A_wu₁}` and `N = {x : v₁A_wx=0 for every w}`. The active realization has
dimension `dim R/(R∩N)=d`; the zero bridge entries give `u₀∈N` and `v₀R=0`. If `u₀∈R`, it adds
one unobservable reachable direction and `v₀` forces one complementary dimension. If `u₀∉R`,
the direct sum `R+Ku₀` is still annihilated by nonzero `v₀`. Both cases give `n≥d+2`.

**Scope:** exact diagonal two-channel identities only. Invertible row and column changes on the
two boundary channels preserve the conclusion. Same-zero series and off-diagonal bridges are
outside the theorem.

**Use:** with [`MM-O04`](#mm-o04-uniform-rank-four-paired-series), this closes every exact
five-state diagonal rank-two bridge for the paired scalar series.

**Formalization:** `twoChannelBoundaryTax` proves the finite-dimensional core, and
`exactDiagonalTwoChannel_card_lower_bound` derives the all-word bridge theorem from an arbitrary
nonsingular finite Hankel section. The proof uses no infinite Hankel library. It is slightly
stronger than the reported statement: nonzero inactive row and column suffice; full boundary
rank two is unnecessary.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O04: Uniform rank-four paired series

**Kind:** certificate
**Evidence:** formalized
**Disposition:** graduated

For every `β≥3` and every tag body, the scalar series

```text
f(w) = ℓ A_w γ,       w ∈ {b,c,t}*
```

of the explicit paired `4 × 4` controls has Hankel rank exactly four. A
body-independent certificate already lies in the subalphabet `{b,t}`. Put

```text
s = 3^β,      p = 3s,      m = (5s−1)/2,
u = 3m+2,     a = 3p.
```

For the `b` control `B`, toggle `T`, row `ℓ`, and column `γ`, the four prefix rows

```text
ℓ, ℓB, ℓB², ℓBT
```

have determinant `48u(13a−15)`. The four suffix columns

```text
γ, Tγ, Bγ, BTγ
```

have determinant `12p(s−3)`. Both are nonzero for `β≥3`, so their product is a
nonzero `4 × 4` Hankel minor. The displayed representation supplies the matching upper
bound.

The same certificate survives

```text
g(w) = λ χ(w) f(w)
```

for `λ≠0` and every nonzero monoid character `χ`, because the Hankel minor changes only
by invertible diagonal row and column scalings.

**Scope:** exact coefficient series over characteristic zero, including similarity, exact
restriction or quotient, and nonzero per-letter rescaling. The result supplies no lower bound
for another series with the same zero set.

**Use:** proves exact minimality of paired-role compression and supplies `d=4` to
[`MM-O03`](#mm-o03-two-channel-boundary-tax). It also closes exact three-state
minimization of the paired route to `M₃(4)`.

**Formalization:** `pairedRankReachable_det` and `pairedRankObservable_det` prove the two
determinant identities. `pairedRankHankel_det_ne_zero` certifies the integer Hankel section,
`paired_exact_state_lower_bound` gives the universal rational four-state lower bound, and
`paired_exact_diagonal_twoChannel_state_lower_bound` composes this record with `MM-O03` to rule
out every exact five-state diagonal two-channel bridge.

**Issue:** [#3, Formalize the exact-realization obstructions for
`M₅(3)`](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/3).

### MM-O05: Width-three scheduled rank

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For deletion width three and every nonempty tag body, the scheduled binary
coefficient series has exact rational Hankel rank five. A symbolic `5×5` minor
using

```text
prefixes = {ε, 0, 1, 00, 10},
suffixes = {ε, 0, 1, 00, 01}
```

factors into explicit reachable and observable matrices with nonzero
determinants. Every exact rational representation therefore has at least five
states; the native scheduled representation has exactly five.

**Scope:** exact coefficients, deletion width three, and nonempty body. The
generic experimental claim `rank=β+2` is not part of the theorem. Same-zero
representations remain outside every Hankel-rank lower bound.

**Artifact:** `MatrixMortality.scheduledWidthThree_exact_state_lower_bound`,
`MatrixMortality.scheduledWidthThreeHankel_det_ne_zero`, and
`MatrixMortality.scheduledWidthThree_native_state_card` in
[`ScheduledBinaryRank.lean`](MatrixMortality/ScheduledBinaryRank.lean).

**Use:** reject exact state compression of the width-three clock below five.
The live fixed-table routes must change the zero series, change the source, or
fuse the clock with a delimiter or mortality interface.

### MM-O06: Pure-power punctuation obstruction

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Lift the paired data matrices and toggle to five dimensions by

```text
Ĝ_x = diag(G_x,0),      T̂ = diag(T,0).
```

For a nonempty tag body, `Ĝ_b` and `Ĝ_c` have a common three-dimensional image
`H` and common kernel `ℚe₅`. Suppose a candidate delimiter `S` realizes an
isolated toggle in every data context:

```text
Ĝ_i S Ĝ_j = Ĝ_i T̂ Ĝ_j,      i,j∈{b,c}.
```

Then `S−T̂` maps `H` into `ℚe₅`. Since `T` fixes the affine and upper-word
directions, `S` has a nonzero fixed vector in their span. Evaluating any proposed
contextual identity

```text
Ĝ_i S^m Ĝ_j = λ Ĝ_i P̂ Ĝ_j,      m≥1, λ≠0,
```

on that vector contradicts the payload action of the paired separator `P=CL`.
No pure delimiter run can therefore serve as the separator while isolated
delimiters retain their exact toggle semantics.

**Scope:** the theorem assumes a nonempty body, exact toggle behavior between
both data contexts, the lifted paired matrices, and punctuation by a pure power
of `S`. It does not exclude a mixed word containing data matrices, approximate
or same-zero toggle semantics, or another representation.

**Use:** reject pure-power variants of the bordered-toggle route. Any surviving
fusion must punctuate with a mixed word.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md).

### MM-O07: Setter parameter rigidity

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

In the five-state setter construction, write

```text
f=(1,0,r)ᵀ,      p=(0,−1,0)ᵀ,      B=[f p q],
C=(μ,−1,t)ᵀ,     C̃=(μ,1,0,1,0)ᵀ.
```

The payload part of the marked boundary is

```text
B(μ,1,0)ᵀ=(μ,−1,μr)ᵀ.
```

Exact alignment with `C` therefore forces

```text
r=t/μ.
```

The parameter is not generic in the displayed source-preserving family. A
reported malformed zero at `r=8735/8978` also fails direct symbolic
multiplication: for `β=3`, body `bbcc`, the claimed word has coefficient

```text
(2r+1)(17956r²−9246r−8709)/(134(r−1)),
```

which is nonzero both at the reported value and at the lawful value `81/67`.

**Scope:** this fixes the parameter only for the displayed basis and marked
boundary. Another construction may introduce genuine free parameters. The
coefficient check rejects the reported counterexample, not all malformed
counterexamples.

**Use:** remove generic-parameter selection from the live proof program. The
projective avoidance problem must be settled at `r=t/μ`.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#parameter-correction).

### MM-O08: Full-algebra prefix pair

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let `B₀,B₁` be the restricted ten-state prefix generators emitted by the current arithmetic
source envelope. The physical word `000` is nonzero rank one:

```text
B₀³=uvᵀ.
```

The ten columns

```text
u, B₁u, …, B₁⁹u
```

and the ten rows `vᵀB_p` for

```text
p∈{ε,1,10,11,101,110,1011,1101,10110,11010}
```

are bases. Their determinant certificates are nonzero uniformly for `β≥3` and
`body.length≥β−1`. The two large polynomial factors reduce respectively to residues `8`
and `3` modulo `9`; only the final reachable pivot uses that the body is nonempty. Hence the
one hundred physical products

```text
B₁ʲB₀³B_p=(B₁ʲu)(vᵀB_p)
```

span every outer product and therefore

```text
span_ℚ{B_w : w∈{0,1}*}=M₁₀(ℚ).
```

The pair has no nonzero proper common invariant subspace or quotient. More strongly, for every
nonzero internal word `E=UW`, the reachable space of `WA_wU` is all of `ℚ¹⁰`, its
unobservable subspace is zero, and its exact block-Hankel rank is ten.

**Scope:** this closes exact linear restriction, quotient, reachable/observable minimization,
and internal-sandwich compression of this physical pair. It does not exclude a different pair,
a different transducer, a same-zero nine-state series, or any nonlinear compiler.

**Use:** stop exact minimization of the present ten-state decoder. Any `M₉(2)` attack must
change the physical pair or change its nonzero behavior.

**Artifact:** the coordinate reconstruction, determinant factors, positivity proof, and
independent symbolic check are in
[`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#the-ten-state-prefix-pair).

**Formalization:** [`MatrixMortality/PrefixContexts.lean`](MatrixMortality/PrefixContexts.lean),
[`MatrixMortality/PrefixContextsClosed.lean`](MatrixMortality/PrefixContextsClosed.lean),
[`MatrixMortality/PrefixContextsNonsingular.lean`](MatrixMortality/PrefixContextsNonsingular.lean), and
[`MatrixMortality/PrefixFullAlgebra.lean`](MatrixMortality/PrefixFullAlgebra.lean), through the
generic exact-behavior bridge in
[`MatrixMortality/FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean);
`prefixAlgebra_zero_cube`, `prefixAlgebraReachable_isUnit`,
`prefixAlgebraObservable_isUnit`, `prefixAlgebra_wordProductSpan_eq_top`, and
`prefixAlgebra_exactSandwich_ten_le_finrank`.

### MM-O09: Two-state ternary prefix image

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

A complete ternary prefix tree with five leaves has exactly two internal states: the root has
two leaf children and one internal child, whose three children are leaves. Consider a literal
exact weighted decoder with one three-dimensional payload space at each state, four nonsingular
leaf payloads, and one singular separator.

At least one child leaf has a nonsingular decoded payload. Its factorization through the
root-to-child edge forces that edge matrix to be nonsingular. The physical generator carrying
that edge therefore supplies the complete root payload block to the joint image. A nonsingular
child completion either occurs on the same physical generator, making it full rank, or its
graph can be combined with the root block to isolate the complete child block. Thus the span
of the three generator images is the full six-state carrier.

**Scope:** literal exact two-state ternary prefix decoders with three-dimensional edge
matrices and exactly the stated four-nonsingular/one-singular source profile. Repairable
quotients, state-dependent gauges, same-zero decoders, and non-prefix codes remain open.

**Use:** a direct ternary recoding of the five-matrix source cannot reach five dimensions by
the common-image compiler [`MM-C02`](#mm-c02-common-image-restriction).

**Artifact:** [`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#secondary-obstructions).

### MM-O10: Additive toggle fusion cycle

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

Normalize the paired separator to an idempotent `P`, and let `T` be the involutive paired
toggle. Since the boundary row obeys `LT=L`, one has `PT=P`. Put

```text
Q=TP,      F=T−P.
```

Then `Q` is rank-one idempotent and

```text
F²=I−Q,      F³=F.
```

Both `F` and `F²` have rank three, so every positive power of `F` is rank three. No pure power
of the most direct additive toggle/separator fusion can punctuate or vanish.

**Scope:** the single ansatz `F=T−P` after idempotent normalization. Bordered couplings,
different perturbations, and mixed words containing data generators remain open.

**Use:** reject the additive fusion before any power search.

**Artifact:** [`audits/internal-sandwich-prefix-algebra-2026-07-25.md`](audits/internal-sandwich-prefix-algebra-2026-07-25.md#secondary-obstructions).

### MM-O11: Full-algebra paired-binary family

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Adjoin the canonical rank-one separator `P=CL` to the two transposed six-state paired-binary
controls. The columns

```text
C, A₀C, A₁C, A₀²C, A₁A₀C, A₀³C
```

and rows

```text
L, LA₀, LA₁, LA₀², LA₀A₁, LA₀³
```

are bases throughout the source envelope `β≥3`. Their determinant factors have final terms
congruent to `3 mod 9`, using only that the rule-`c` lower word ends in `10`. Consequently the
thirty-six physical contexts

```text
A_uPA_v=(A_uC)(LA_v)
```

span `M₆(ℚ)`.

Every nonzero internal word therefore has reachable space `ℚ⁶`, zero unobservable subspace,
and exact sandwich dimension six. [`MM-C04`](#mm-c04-internal-word-sandwich-minimization)
cannot reduce this family to five states.

**Scope:** the paired-binary mortality family only. A modular sweep found full algebra for all
120 literal CHHN packings at `β=3`, body `bb`, but that bounded computation is not an unbounded
theorem.

**Use:** close exact invariant restrictions, quotients, and internal-word sandwiches of the
canonical `Z₆(2)→M₆(3)` construction. A five-state proof must change the physical family or its
nonzero behavior.

**Artifact:** the symbolic determinant proof and bounded CHHN sweep are in
[`audits/six-state-sandwich-saturation-2026-07-25.md`](audits/six-state-sandwich-saturation-2026-07-25.md);
the executable certificate is
[`tools/audit_six_state_sandwich.py`](tools/audit_six_state_sandwich.py).

Lean proves the sparse context matrices invertible by eliminating their kernels. The final
reachability and observability pivots reduce to integer expressions of the form `9z+3`, using
the terminal lower suffix `10`. A generic rank-one-context theorem then turns the thirty-six
physical contexts into a spanning family.

**Formalization:** [`MatrixMortality/FullMatrixAlgebra.lean`](MatrixMortality/FullMatrixAlgebra.lean),
[`MatrixMortality/PairedBinaryContexts.lean`](MatrixMortality/PairedBinaryContexts.lean),
[`MatrixMortality/PairedBinaryContextsClosed.lean`](MatrixMortality/PairedBinaryContextsClosed.lean),
[`MatrixMortality/PairedBinaryContextsNonsingular.lean`](MatrixMortality/PairedBinaryContextsNonsingular.lean), and
[`MatrixMortality/PairedBinaryFullAlgebra.lean`](MatrixMortality/PairedBinaryFullAlgebra.lean),
through the generic exact-behavior bridge in
[`MatrixMortality/FullMatrixBehavior.lean`](MatrixMortality/FullMatrixBehavior.lean);
`pairedBinaryMortality_wordProductSpan_eq_top` and
`pairedBinaryMortality_exactSandwich_six_le_finrank`.

### MM-M01: Off-diagonal companion interface

**Kind:** partial mechanism  
**Evidence:** audited  
**Disposition:** stock

For `g(w)=λB_wd`, invertible `B_a`, and `α=λd≠0`, define

```text
J(x) = [[0,x],[1,0]].
```

In dimension `r+1`, put

```text
u₀ = e_{r+1},           u₁ = (d/α,0)ᵀ,
v₀ = (λ,0),             v₁ = e_{r+1}ᵀ,
U  = [u₀ u₁],           V  = [v₀;v₁],
E  = UV.
```

Then `rank E=2` and

```text
V diag(B_w,1) U = J(g(w)/α).
```

Products fracture at `E`, and a central product of `J` matrices can vanish only if a bridge
coefficient vanishes. Repeating one zero bridge twice gives `J(0)²=0`.

**Scope:** as a standalone scalar-to-mortality compiler this is dominated by the rank-one
separator `P=dλ`, which stays in dimension `r`. A four-state binary root would therefore prove
`M₄(3)`, not merely `M₅(3)`.

**Use:** retain `J` only as a target interface when punctuation must be represented by a word in
another generator rather than adjoined as its own generator.

**Next:** use the off-diagonal interface in the fused-toggle search; do not present it as a new
frontier reduction.

### MM-M02: Bordered toggle

**Kind:** partial mechanism  
**Evidence:** audited  
**Disposition:** parked

Choose a two-plane `F` in the `+1` eigenspace of the paired toggle, complete it by a third
`+1` eigenvector `g`, a `−1` eigenvector `h`, and a fifth vector `η`. In the basis
`(F,g,h,η)`, put

```text
S = I_F ⊕ K,             K = [[1,0,1],[0,−1,1],[−1/2,−1/2,0]].
```

Its upper-left four-dimensional block is the original toggle, and

```text
rank S = 4,     rank S² = 3,     S³ = Π_F,     rank Π_F = 2.
```

With data lifts `diag(G_x,0)`, every word containing no adjacent toggles has the original
four-dimensional control product as its upper-left block and is therefore nonzero. Maximal
toggle runs have three modes: `S`, `S²`, and `Π_F`.

**Scope:** mixed `S²` runs, malformed placements of `Π_F`, and the required rank-one or
off-diagonal selector are unresolved. Bounded searches on one benchmark do not establish an
impossibility theorem.

**Use:** a concrete architecture for fusing the toggle and separator into the third physical
generator of an `M₅(3)` family.

**Next:** parameterize the permitted fifth-coordinate couplings, solve the selector identities
symbolically, and prove a global maximal-run grammar or a symbolic no-go theorem.

### MM-M03: Five-state setter punctuation

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

Let `r=t/μ`, put

```text
f=(1,0,r)ᵀ,      p=(0,−1,0)ᵀ,
q=(0,0,2r(1−r))ᵀ,      B=[f p q],
α=1+2r,          λ=α/μ,
```

and conjugate the three-dimensional rule matrices by `B`. Two marker
coordinates produce explicit rational `5 × 5` data matrices `A_b,A_c` and a
delimiter `S`. The latter satisfies

```text
rank S=3,      rank S²=2,      rank S³=1,
Sⁿ=S³ for n≥3.
```

Every data matrix clears the markers. On words without `S²`, an isolated
delimiter immediately to the right of a data letter selects its erasure role;
absence of a delimiter selects its rule role. The marked terminal column makes
the rightmost data letter an erasure. This is an exact total decoder on the
regular physical language and represents every lawful source history.

For the distinguished letter `c`, the mixed word

```text
E=S²A_cS³
```

obeys the exact rank-one identity

```text
E=λC̃L̃.
```

Hence `EWE=0` exactly when `L̃WC̃=0`. A source halting witness therefore gives a
zero word over the three five-state generators `{A_b,A_c,S}`.

**Scope:** this proves the regular-word semantics, internal separator, and
halting-to-mortality implication. It does not prove the converse: arbitrary
words may contain maximal delimiter runs of length two.

**Use:** this is the concrete mixed-word successor to the parked bordered
toggle. Combine it with [`MM-S01`](#mm-s01-square-run-projective-normal-form);
do not claim `M₅(3)` until projective avoidance is proved.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#side-normal-data).

**Next:** formalize the displayed matrices, regular decoder, power identities,
and separator identity.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-M04: Swapped-digit setter

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

Reverse the ordinary nonzero ternary digit embedding:

```text
0↦2,       1↦1.
```

Word equality, concatenation, length, and the entire Neary source theorem are
unchanged. Put

```text
ρ=3^β,       μ=2ρ−1,       t=3ρ,       r=t/μ,
H=5ρ−1,      R=2−ρ,
f=(1,0,r)ᵀ, p=(0,−1,0)ᵀ, q=(0,0,r(2−r))ᵀ.
```

The same five-state setter construction, with `α=1+r`, satisfies

```text
rank S=3,      rank S²=2,      rank S³=1,
Sⁿ=S³  for n≥3,
S²A_cS³=λC̃L̃.
```

The regular rule/erasure decoder and the source-halting-to-mortality
implication therefore survive exactly.

For every square-run block, the induced projective matrix has determinant

```text
κVA>0,       κ=(1+r)/(μ(2−r)).
```

Thus every transfer is orientation preserving. In the scaled coordinate its
common center is

```text
h=H/R<0,
```

whereas every pole `P/V` is positive.

**Scope:** the sign separation does not itself prove avoidance. Arbitrary
iterations can cross the center, and the remaining fixed-slope correspondence
equations are asynchronous.

**Use:** this is the preferred setter variant. Unlike
[`MM-M03`](#mm-m03-five-state-setter-punctuation), it has a one-sided centered
coefficient and the finite-slope theorem
[`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction).

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** formalize the parametric digit-order construction and decide the
finite nonterminal slopes exposed by `MM-S07`.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S01: Square-run projective normal form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For the candidate in [`MM-M03`](#mm-m03-five-state-setter-punctuation), the
image of `S²` is the two-plane

```text
J={(a,x,0,x,0)ᵀ : a,x∈ℚ}.
```

If a regular intervening block has side product

```text
M_z=[[1,V,U],[0,B,0],[0,0,A]],
```

its action between square runs is represented on `J` by

```text
F_z =
[[1+rU,       −V],
 [κ(A−1−rU),  κV]],

κ=(1+2r)/(2μ(1−r)).
```

The determinant `κVA` is nonzero. Thus a segment containing square runs but no
`S³` cannot collapse by rank loss. On the affine projective chart, it acts by

```text
Φ_z(x)=κ(A−1−rU+Vx)/(1+rU−Vx)
```

and vanishes exactly when the current state reaches the pole

```text
π_z=(1+rU)/V.
```

Runs of length at least three equal the rank-one map `S³` and fracture every
arbitrary product into such projective bridges. The possible reset values are
`0` and `1/μ`. At `1/μ`, the pole equation is

```text
(μ+tU−V)/μ=0,
```

which is precisely the original terminal-match equation.

Consequently, the full mortality converse for `{A_b,A_c,S}` is equivalent to
the following avoidance property: every finite orbit generated by the
admissible maps `Φ_z`, starting at `0` or `1/μ`, avoids every pole except a
genuine terminal-match pole reached from `1/μ`.

**Scope:** the projective normal form and equivalence are proved for the
displayed candidate at the forced value `r=t/μ`. The avoidance property itself
is open. No bounded search certifies it.

**Use:** replaces an unstructured malformed-word grammar by a one-dimensional
rational dynamical problem. A proof of avoidance completes `M₅(3)`; one
nonterminal pole orbit refutes this candidate.

**Artifact:** [`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md#square-run-transfer).

**Next:** seek a finite invariant based on congruences, `3`-adic valuation and
pulse phase, signed intervals, or self-synchronizing code suffixes. Search
states are projective values, not five-dimensional vectors.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S02: Reset-zero projective peeling

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Scale the projective coordinate in [`MM-S01`](#mm-s01-square-run-projective-normal-form) by
`y=μx` and put

```text
h=(17ρ−1)/(2(ρ+1)),      ρ=3^β.
```

For a nonempty role block `z`, let

```text
P_z=[spell(nearyUpper,z)·10^β]₃,
V_z=[spell(nearyLower,z)]₃,
A_z=3^|spell(nearyUpper,z)|.
```

Then

```text
Ψ_z(y)=h(1−μA_z/(P_z−V_zy)),      π_z=P_z/V_z.
```

Every pole lies in one of two exact `3`-adic shells:

```text
v₃(π_z−h)=β  if z is one erasure role,
v₃(π_z−h)=1  otherwise.
```

For an orbit leaving the ordinary reset,

```text
v₃(Ψ_u(0)−h)=|spell(nearyUpper,u)|.
```

Equality with a pole therefore forces that upper length to be `1` or `β`. Length one gives
`Ψ_u(0)=1`, and a pole at `1` is precisely a genuine terminal match. Length `β` forces `u`
to consist only of `c` roles, but its image is smaller than both single-erasure poles.

**Scope:** excludes a false pole after one preceding transfer from reset `0`. It does not
control longer orbits or one-transfer images from the distinguished boundary `1`.

**Use:** any counterexample to the setter candidate must contain at least two nontrivial
projective transfers after an ordinary reset. Future invariants should track `3`-adic mismatch
depth together with the pulse or suffix state.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md).

**Next:** lift the shell calculation from valuation alone to a finite suffix-carry state.
Residue-only projective abstractions saturate on the benchmark and cannot prove avoidance.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S03: Centered setter carry

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Retain the scaled coordinate and constants of
[`MM-S02`](#mm-s02-reset-zero-projective-peeling), and put

```text
H=(17ρ−1)/2,      R=ρ+1,      K=RHμ,
C_z=RP_z−HV_z,    m_z=|spell(nearyUpper,z)|.
```

Represent a finite projective state by integers `X,Y` through

```text
y−H/R=−HμX/Y.
```

One admissible square-run block acts exactly by

```text
X'=3^m_zY,
Y'=C_zY+KV_zX.
```

The two reset states are `(1,Rμ)` and `(3,RH)`. A pole is exactly a zero
second coordinate. If `d=v₃(X)−v₃(Y)` and
`s_z=v₃(C_z)∈{1,β}`, then away from the equal-valuation branch

```text
d'=m_z−min(d,s_z).
```

At equal valuation, the extra valuation is the carry created by the two
normalized units; infinite carry is precisely a pole. For blocks ending in an
erasure, the first unit test is fixed: a multi-role pole requires normalized
unit `1 mod 3`, while a single-erasure pole requires `2 mod 3`.

This recurrence yields two exact gates.

1. After two transfers from reset zero, outside the intermediate state `1`, a
   prospective third pole is possible only when the second block is two
   `c` roles, when it is `β+1` `c` roles, or when the first block is two
   `c` roles and the second block is the single `b` erasure.
2. From the distinguished boundary `1`, one completed block reduces
   projectively to `(3^m,R(P−V))`. If it is not already a terminal match, a
   following pole requires

   ```text
   v₃(P−V)=m−1     or     v₃(P−V)=m−β.
   ```

   This valuation is exactly the common binary-suffix length of the encoded
   upper boundary and lower spelling.

**Scope:** these are necessary gates, not a proof of arbitrary-depth
avoidance. The first and prospective pole blocks remain unbounded, and the
equal-valuation carry can retain an arbitrarily long synchronized suffix.

**Use:** replaces raw Möbius iteration by an integer carry automaton and
identifies the only place where the Neary pulse state must be attached. Search
the three two-transfer block shapes first; any general proof must control the
two suffix equations at the distinguished boundary.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#centered-integer-carry).

**Next:** apply [`MM-S04`](#mm-s04-reverse-suffix-discrepancy) to quotient the
word-valued suffix carry without forgetting the two resonant target families.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S04: Reverse suffix discrepancy

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let `M=10^β`, and compare the terminal words `U(z)M` and `V(z)` of an arbitrary
Neary role word `z`. Reading roles from right to left, maintain the pair
obtained by reversing both words and deleting their common prefix. Prepending
one role appends its reversed upper and lower images to the two residuals,
after which their new common prefix is deleted. Until the first mismatch, at
least one residual is empty; once both are nonempty, their first bits differ
and no unprocessed role can change the common suffix.

This recurrence computes exactly

```text
k=lcs(U(z)M,V(z)).
```

Put `m=|U(z)|` and `d=m−k`. If the first mismatch occurs in a processed suffix
`q`, with `z=pq`, then

```text
|U(p)|≤d+|M|.
```

If no mismatch occurs and `d>0`, the surviving upper residual has exactly
`d+|M|` bits. The only setter resonances are `d=1` and `d=β`, so their
unprocessed left fringes have upper length at most `β+2` and `2β+1`.

**Scope:** the natural exact state is a residual word. This theorem neither
bounds that queue before the first mismatch nor proves that no finite semantic
quotient exists. It proves no projective avoidance statement by itself.

**Use:** replaces the proposed finite pulse transducer by the correct
PCP-discrepancy object. A successful proof must recognize reachability of two
bounded residual target families through a quotient compatible with role
prepending. Phase, length, valuation, and fixed-modulus residue alone do not
retain the exact recurrence; the tested residue-only quotients saturate.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#reverse-suffix-discrepancy-queue);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** combine the discrepancy queue with
[`MM-S05`](#mm-s05-distinguished-boundary-beta-shell), then identify a semantic
quotient for the surviving valuation-one target.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S05: Distinguished-boundary β-shell

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

Start the setter carry at projective boundary `1`. For a nonterminal block
`v`, put

```text
m=|U(v)|,       k=lcs(U(v)M,V(v)),       d=m−k,
Δ=(P_v−V_v)/3^k.
```

Then `Δ` is an integer not divisible by `3`, and the resulting centered state
is projectively `(3^d,RΔ)`. If a following block `z` is a pole, it must satisfy

```text
C_zΔ+HμV_z3^d=0.
```

When `d=β`, the pole-shell theorem forces `z` to be a single erasure. The
`b` erasure requires

```text
Δ=−2Hμ/(45ρ²+53ρ−10),
```

which lies strictly between `−1` and `0`. The `c` erasure requires `Δ=−μ`.
The latter equality would make the addition

```text
P_v+μ3^{m−β}=V_v
```

force the binary factor `0·1·0^β` inside
`tagEncode β (v.map letter)·M`. That factor is impossible: every occurrence of
`1·0^β` begins a `b` codeword or the final marker and is never preceded by
`0`.

Therefore no finite nonterminal block in the distinguished-boundary
`β`-resonance can be followed by a pole.

**Scope:** this closes only the `d=β` branch immediately after boundary `1`.
It does not handle the surviving `d=1` discrepancy, nor β-shell states reached
after other malformed transfers.

**Use:** remove the single-erasure pole family from the boundary-one analysis.
The remaining semantic quotient needs to preserve only valuation-one target
blocks.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#elimination-of-the-beta-shell);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** apply
[`MM-S06`](#mm-s06-valuation-one-divisor-normal-form) to the surviving
valuation-one shell.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S06: Valuation-one divisor normal form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let a multi-role pole block have positive codes `P,V` and

```text
C=RP−HV,       v₃(C)=1.
```

Suppose an integer `3`-adic unit `Δ` reaches that pole:

```text
CΔ+3HμV=0.
```

Reduce `P,V` by their gcd:

```text
P=gp,       V=gv,       gcd(p,v)=1,
a=(Rp−Hv)/3.
```

Put `q=gcd(a,v)`. Then

```text
q=gcd(R,v),       q∣R.
```

Writing `a=qa₀`, `v=qv₀`, and `r=R/q` gives

```text
gcd(a₀,v₀)=gcd(r,v₀)=1,
a₀Δ=−Hμv₀,
rp=Hv₀+3a₀.
```

In particular,

```text
a₀∣Hμ,       v₀∣Δ.
```

Every integral pole therefore lies on one of finitely many arithmetic rays
indexed by divisors `q∣R` and `a₀∣Hμ`; only `v₀` remains unbounded.

Moreover,

```text
Δ=H       ↔       P=V.
```

Thus the distinguished integral value is exactly the genuine terminal-match
pole, not a malformed one.

For a boundary discrepancy with `d=1`, positivity also gives

```text
0<Δ<9ρ.
```

Values `Δ≤3μ` map to a nonpositive projective point and cannot be poles.
Hence the positive branch is confined to the finite interval
`3μ<Δ<9ρ`; only negative divisor rays remain unbounded.

**Scope:** the divisor normal form does not prove that the other rays are
empty. Their realizability by a common Neary role word remains open. The exact
benchmark search through target-block length `14` finds no false integral
unit pole, but that is computational evidence only.

**Use:** replace an unconstrained rational-pole search in the valuation-one
shell by finitely many divisor rays. Positive boundary discrepancies are
already bounded by their `β+2`-digit unmatched upper prefix; negative rays
remain the unbounded branch.

**Artifact:** [`audits/setter-projective-peeling-2026-07-25.md`](audits/setter-projective-peeling-2026-07-25.md#valuation-one-divisor-normal-form);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** intersect the divisor rays with the reverse Neary role transducer.
Either prove that only `(a₀,v₀)=(-μ,1)` is realizable, or return the first
explicit false integral pole.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S07: Swapped-digit finite-slope reduction

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

For the swapped setter [`MM-M04`](#mm-m04-swapped-digit-setter), put

```text
D=ρ−2=−R>0.
```

Every nonempty block has

```text
C=RP−HV=−(DP+HV)<0.
```

At the distinguished boundary, a valuation-one pole reached from a normalized
integer discrepancy `Δ` must satisfy

```text
(DP+HV)Δ=3HμV.                              (1)
```

Consequently

```text
0<Δ<3μ.
```

Reduce `P=gp`, `V=gv`, with `gcd(p,v)=1`, and put

```text
q=gcd(D,v),       D=qd,       v=qv₀.
```

Equation (1) becomes

```text
Δ(dp+Hv₀)=3Hμv₀.
```

Because `gcd(dp+Hv₀,v₀)=1`,

```text
dp+Hv₀ ∣ 3Hμ.
```

Thus every integral valuation-one pole belongs to an effectively finite set:

```text
q∣D,       v₀<3μ,       p≤3Hμ/d.
```

There is no unbounded divisor ray. The distinguished value remains exact:

```text
Δ=H       ↔       P=V.
```

In the `β`-shell, the single `b` erasure requires a rational discrepancy
strictly between `1` and `2`, while the single `c` erasure requires `Δ=2μ`.
The latter is excluded by
[`MM-S08`](#mm-s08-swapped-distinguished-boundary-beta-shell).

**Scope:** finiteness of the primitive slopes is not finiteness of the target
role words: the common multiplier `g` remains unbounded. One of the slopes is
the original undecidable terminal equality. The theorem therefore narrows but
does not decide projective avoidance.

**Use:** replace the ordinary setter's unbounded negative rays by finitely many
fixed-ratio correspondence languages. The next proof should show that every
nonterminal accepted slope either contains a genuine terminal-match suffix or
violates the Neary pulse invariant.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#one-sided-centered-carry);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** prove or refute the finite-slope endpoint theorem in the sole
remaining valuation-one shell.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S08: Swapped distinguished-boundary beta shell

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

For the swapped setter, suppose a distinguished-boundary block has resonance
gap `d=β`.  If it could hit the single `c`-erasure pole, its normalized
discrepancy would be `Δ=2μ`.  After deleting the common suffix, the upper and
lower binary prefixes would necessarily have the form

```text
A=T·00·z·10,       B=T·11·z·01,
|T|=β−1,           |z|=β−2.
```

This is the unique carry pattern for

```text
[A]₃−[B]₃=2μ
```

under the swapped nonzero-digit embedding.

The upper pattern forces its source-letter prefix to be

```text
c^s·b·c^(β−s−3),       0≤s≤β−3,
```

followed by another `b` or by the marker.  It therefore forces the lower
prefix

```text
1^(s+1)·0^(β−s−2)·11·0^s·1^(β−s−2)·01.
```

For `s=0`, neither lower image of a `b` role has the required prefix.  For
`s>0`, the first role must be the `c` rule.  Its body must begin
`c^(s−1)b`, after which the `b` code supplies `β` zeros where the target
prefix permits only `β−s−2`; the only alternative contradicts
`|body|≥β−1`.  Hence `Δ=2μ` is impossible.

The single `b`-erasure pole was already excluded because its required
discrepancy lies strictly between `1` and `2`.  Thus the complete
distinguished-boundary `β` shell is pole-free.

**Scope:** later malformed transfers can re-enter a `β`-adic valuation shell
from projective states other than the distinguished boundary.  This theorem
does not classify those states.

**Use:** all distinguished-boundary danger is now concentrated in the
valuation-one finite-slope languages of
[`MM-S07`](#mm-s07-swapped-digit-finite-slope-reduction).

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#elimination-of-the-beta-shell);
[`tools/explore_setter_projective.py`](tools/explore_setter_projective.py).

**Next:** intersect each surviving primitive slope with the reverse
discrepancy language; a hit need only imply a genuine terminal suffix.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S09: Canonical swapped residue cannot hit a pole

**Kind:** obstruction
**Evidence:** audited
**Disposition:** active

The distinguished-boundary word `D_c^(β+1)` has

```text
d=1,       Δ₀=(9ρ−5)/2.
```

If this state met a valuation-one pole with side codes `P,V`, the pole
equation would reduce to

```text
D(9ρ−5)P=H(3ρ−1)V.
```

Modulo `ρ`, the left coefficient is `10`, `P≡−1`, and the right coefficient
is `1`.  Hence

```text
V≡ρ−10 (mod ρ).
```

The corresponding binary suffix under the swapped digit embedding is

```text
0^(β−3)100.
```

An admissible target block ends in an erasure.  Its lower word either contains
no rule and hence no `1`, or its last rule followed by one erasure ends in
`1100`; any other number of trailing erasures gives the wrong terminal zero
run.  Therefore the required suffix is impossible for `β≥4`.

**Scope:** this excludes one recurrent positive boundary residue, not every
positive `d=1` discrepancy.  It uses the target block's final-erasure
grammar.

**Use:** the Neary compiler has `β=10·period`, so the canonical all-erasure
branch is harmless for every emitted instance.  Any remaining
distinguished-boundary pole must come from a noncanonical positive near-match,
which is now a semantic source-halting question.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#canonical-valuation-one-residue).

**Next:** prove that every other positive `d=1` near-match already implies
source halting.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

### MM-S10: Swapped target-suffix sieve

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** active

Let a positive `3`-adic unit `Δ` meet a valuation-one target pole with side
codes

```text
P=μ+tU,       V>0.
```

The pole equation is

```text
ΔDP=H(3μ−Δ)V.
```

Every nonempty upper role word ends in binary `1`.  Hence `P`, modulo
`9ρ=3^(β+2)`, is the swapped code of `11·0^β`, namely `H`.  Both `H` and
`3μ−Δ` are units modulo `3`, so cancellation gives the fixed target suffix

```text
V ≡ σ_Δ := ΔD(3μ−Δ)⁻¹ (mod 9ρ).
```

This is an effective necessary suffix test.  If the lower word has at least
`β+2` letters, all `β+2` digits of the fixed-width residue must be nonzero and
its swapped binary decoding must obey the lower-role suffix grammar.  If the
lower word is shorter, then necessarily `V=σ_Δ`; only the canonical
base-three digits are word digits, while the leading zero padding is
harmless.  Thus a residue with an internal zero digit is impossible, and a
shorter all-nonzero residue leaves only the single exact candidate
`V=σ_Δ`.

In particular, for

```text
Δ=ρ−1
```

one has

```text
σ_Δ=8ρ−1,
```

whose `β+2` ternary digits are `21·2^β` and whose swapped binary suffix is

```text
01·0^β.
```

No lower spelling can contain this factor.  Every occurrence of `1·0^β`
inside a rule word is preceded by `1`; after an erasure, the next rule begins
with `11`.  Thus `Δ=ρ−1` cannot meet any target pole.

**Scope:** this is a necessary suffix sieve, not a classification of all
positive boundary discrepancies.  Residues passing the sieve still require
semantic or higher-carry analysis.

**Use:** apply before any target-word search.  It eliminates the principal
nonhalting positive residue found in the `β=4` small-envelope census and turns
many other candidate values into immediate digit contradictions.

**Artifact:** [`audits/m53-swapped-setter-2026-07-25.md`](audits/m53-swapped-setter-2026-07-25.md#target-suffix-sieve).

**Next:** classify the boundary values whose `σ_Δ` is a legal lower suffix;
the surviving nonterminal values must then be intersected with the reverse
Neary discrepancy.

**Issue:** [#6, Formalize the five-state setter candidate and decide projective
avoidance](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

## Rank-Three Binary Frontier

### R32-S01: Split return normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

Let `A` be a unit and let `B=UV`, where `U` and `V` have explicit left and right inverses.
Every binary word containing `B` fractures into powers of `A` between copies of `B`, and

```text
B A^n₁ B ⋯ A^nₖ B = U (VA^n₁U) ⋯ (VA^nₖU) V.
```

Therefore `{A,B}` is mortal exactly when a finite product of return matrices `VAⁿU` is zero.
The converse covers every physical word, including empty runs and exterior powers of `A`.
The statement is dimension-free and valid over every nontrivial commutative semiring with the
displayed splittings.

**Scope:** a rank-two `3 × 3` cut over a field satisfies the splitting hypotheses after choosing
bases for its image and coimage. The theorem does not decide the resulting infinite return
family.

**Artifact:** `ReturnFamily.pairGenerator_isMortal_iff`,
`blockedProduct_eq_zero_iff`, and `returnHankel_card_le` in
[`ReturnFamily.lean`](MatrixMortality/ReturnFamily.lean).

**Use:** this is the canonical rank-`(3,2)` normal form. New attacks should modify or classify
the third-order return recurrence `VAⁿU`, not parse binary words again.

### R32-S02: Two-plane edge square

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** graduated

For split finite-rank generators `Aᵢ=UᵢVᵢ`, every nonempty word is zero exactly when the
corresponding adjacent-edge product is zero:

```text
Cᵢⱼ = VᵢUⱼ,       Aᵢ₁⋯Aᵢₙ=0  ↔  Cᵢ₁ᵢ₂⋯Cᵢₙ₋₁ᵢₙ=0.
```

Conversely, four `2 × 2` edges indexed by two vertices assemble into two `3 × 3` generators
whenever the two edges entering each target agree on one shared source line. If one incoming
edge per target is split, both ambient generators have rank exactly two and their mortality is
the constrained edge-path problem.

**Scope:** this is an exact graph reduction and realization theorem. It does not erase the
two-vertex path constraint or prove that every resulting constrained projective problem is
equivalent to unconstrained `M₂(3)`.

**Artifact:** `EdgeCompression.isMortal_iff_exists_edgeProduct_eq_zero`,
`TwoPlaneEdges.output_mul_input`, `TwoPlaneEdges.generator_rank`, and
`TwoPlaneEdges.isMortal_iff_exists_edgeProduct_eq_zero` in
[`EdgeCompression.lean`](MatrixMortality/EdgeCompression.lean) and
[`TwoPlaneEdges.lean`](MatrixMortality/TwoPlaneEdges.lean).

**Use:** analyze rank-`(2,2)` pairs as a two-node graph of invertible and rank-one Möbius edges.
Do not attribute an independent controller bit to the two planes.

### R32-O01: Rank-one profile collapse

**Kind:** obstruction
**Evidence:** audited
**Disposition:** stock

If one binary generator is invertible and the other has rank one, the split-return theorem
reduces mortality to one scalar return

```text
vAⁿu = 0.
```

Cayley–Hamilton makes this an algebraic linear recurrence of order at most three. Skolem
decidability through order four therefore decides the profile. If both generators have rank
one, one-dimensional edge compression reduces mortality to finitely many adjacent scalar
tests.

**Scope:** the unit/rank-one return algebra is Lean-checked. The case of a second singular
generator and the decision theorem are independently audited; the latter is imported from
[Bacik](references/bacik-2025-order-four-skolem.md). This record does not supply a Lean
implementation of the Skolem algorithm.

**Artifact:** `ReturnFamily.rankOnePair_isMortal_iff` and
`ReturnFamily.wordProduct_unitSquare_eq_zero_iff` in
[`ReturnFamily.lean`](MatrixMortality/ReturnFamily.lean).

**Use:** remove every rank-one binary profile from the undecidability search. The only
structurally new profile is one unit and one rank-two matrix.

### R32-S03: ReturnSquare normal form

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

ReturnSquare takes

```text
A=diag(1,q,q²),       B=UV,
VAⁿU = T_c(qⁿ) =
  [(c+1)q²ⁿ−1   qⁿ]
  [c              qⁿ].
```

For integer `q≥2` and `c≠−1`, `A` is a unit and `B` has rank two. The zero-wait return
`T_c(1)=[1,1]ᵀ[c,1]` is an internal rank-one separator; every positive-wait return is a unit.
Physical mortality is therefore equivalent to one scalar bridge

```text
[c,1] T_c(q^n₁)⋯T_c(q^nₖ) [1,1]ᵀ = 0,       nᵢ≥1.
```

The projective action, squaring rail, target strip, reachable determinant, observable
determinant, exceptional parameter `c=−1`, and arbitrary-word converse are exact Lean
theorems.

**Scope:** ReturnSquare is a candidate family, not an undecidability reduction. Its parameter is
a fixed rational input, not writable storage.

**Artifact:** `ReturnSquare.physical_isMortal_iff_positiveBridge`,
`physical_isMortal_iff_oneReturn_or_longBridge`, `cut_rank`, and the projective identities in
[`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean).

**Use:** test arithmetic walls and same-zero modifications on a fully normalized rank-`(3,2)`
laboratory without reopening the physical-word grammar.

**Continuation:** [#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-O02: Two-return square cage

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The scalar coefficient of two positive returns factors through a quadratic in `c`. For integral
return scales `x,y≥2`, its discriminant lies strictly between `N²` and `(N+2)²`; parity excludes
the middle square. Hence the quadratic has no rational root. Every nonresonant ReturnSquare zero
contains at least three positive returns.

**Scope:** this excludes two-return bridges only. One-return resonances
`c=−q^−n` are genuine zeros. Prime-power bases are completely classified by `R32-D02`; a
length-at-least-three residue remains only for bases with several prime factors.

**Artifact:** `ReturnSquare.twoReturnDiscriminant_not_isSquare`,
`twoReturnCore_ne_zero`, `positiveBridge_pair_ne_zero`, and
`positiveBridge_zero_shape` in [`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean).

**Use:** any proposed kill must first exhibit a genuinely three-return mechanism or change the
return pencil.

### R32-O03: Reversible stack state tax

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

The literal reversible projective operation exchanging `t` with `κt²` has return matrix

```text
[1−κt   −t]
[−κ    κt−1].
```

Its two-time block Hankel determinant is `κ²(q−1)⁴`. For `κ≠0` and `q≠1`, every exact return
realization therefore needs at least four ambient states.

**Scope:** this is an exact-series lower bound for the displayed reversible push/pop operation.
It does not exclude a different three-state series with the same zero behavior.

**Artifact:** `ReturnSquareTax.finiteReturnHankel_det` and
`reversibleStack_card_lower_bound` in
[`ReturnSquareTax.lean`](MatrixMortality/ReturnSquareTax.lean).

**Use:** do not add a literal reversible stack to ReturnSquare. A viable storage mechanism must
change nonzero values, use arithmetic residue, or abandon this two-mode return operation.

### R32-O04: Quadratic-pencil verification collapse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let

```text
K(t)=C₀+tC₁+t²C₂.
```

Two complementary rigidity theorems hold over every linear ordered field.

1. If every `Cᵢ` is singular and `K(t)` projectively exchanges `t` with `κt²` for every `t`,
   where `κ≠0`, then all three coefficient matrices vanish.
2. If `K(t)` sends `t` to `t²` while `K(qt)` sends `t` to `qt²` for every `t`, where
   `q∉{0,1}`, then

   ```text
   K(t)=h(t) diag(t,1)
   ```

   for one scalar linear polynomial `h`. Projectively this is blind scaling `z↦tz` on every
   input, not an equality test.

**Scope:** these are exact projective identities for quadratic pencils. The first theorem
models a diagonal three-state realization whose three spectral coefficients each have rank at
most one. Neither theorem excludes a same-zero pencil, a nonsplit cubic action, or verification
restricted to a sparse set rather than a polynomial identity.

**Artifact:** `ReturnSquareNoGo.threeMode_swap_eq_zero` and
`verifiedPush_eq_blindScale` in
[`ReturnSquareNoGo.lean`](MatrixMortality/ReturnSquareNoGo.lean).

**Use:** abandon reversible stack completion inside the split `1,t,t²` architecture. A surviving
return pencil must use an irreducible ambient action, arithmetic carries, or changed nonzero
behavior.

### R32-O05: Jordan parity verifier collapse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

A nonsemisimple ambient mode can carry the term `n(−1)ⁿ`, so the split quadratic-pencil
obstructions do not apply. Imposing the exact natural-number rails

```text
n even: n ↦ n/2,       n odd: n ↦ 3n+1
```

on `Kₙ=C₀+(−1)ⁿC₁+n(−1)ⁿC₂` first forces a five-parameter coefficient normal form. Requiring
the constant and drift modes to be singular, the zero return to be a separator, the alternating
mode to be tangent to the rank-one locus, and the first positive return in each parity to be
invertible leaves one nondegenerate branch up to scalar.

That branch is not a mortality compiler. Its integral physical pair preserves the line through
`(0,1,0)ᵀ` modulo seven: the Jordan generator acts by `−1` and the cut by `1`. Every product is
therefore nonzero in the finite quotient, hence nonzero over `ℤ`.

**Scope:** the uniqueness theorem is conditional on the displayed exact rails and explicit
rank-compatibility hypotheses. It does not classify every Jordan pencil, sparse rail, or
same-zero realization.

**Artifact:** `ReturnJordan.rail_normal_form`, `normalForm_unique`, and
`not_isMortal_generator` in
[`ReturnJordan.lean`](MatrixMortality/ReturnJordan.lean).

**Use:** do not reopen the literal parity-Collatz Jordan branch. A nonsemisimple candidate must
alter the rail, relax exact values, or defeat the finite-ray certificate.

### R32-D01: ReturnSquare immortality walls

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** stock

ReturnSquare is immortal in two large parameter regions:

```text
c ≥ 0,
c = −d  with  d > 1 + (q−1)/q².
```

The second wall is projective. Put

```text
s_d(t)=(d−1)t²+1,       β_d(q)=q/s_d(q).
```

The double cone representing slopes `(0,β_d(q)]` is backward invariant under every positive
return with scale `t≥q`. Pulling a zero bridge through its first return places the residual
vector in that cone; repeated backward invariance would place `[1,1]` there, contradicting
`β_d(q)<1`. The homogeneous proof is sign-invariant and never divides by a projective
denominator.

**Scope:** the inequality is a sufficient uniform wall, not a claimed optimal boundary.
[`R32-D02`](#r32-d02-prime-power-returnsquare-classification) closes the entire middle strip at
prime-power bases. The unresolved strip now concerns bases with at least two distinct prime
factors.

**Artifact:** `ReturnSquare.not_physical_isMortal_of_nonneg`,
`negativeStep_preimage_trap`, `transfer_neg_preimage_signedTrap`, and
`not_physical_isMortal_of_beyond_negative_wall` in
[`ReturnSquare.lean`](MatrixMortality/ReturnSquare.lean) and
[`ReturnSquareDynamics.lean`](MatrixMortality/ReturnSquareDynamics.lean).

**Use:** remove broad sign regions from searches and reuse the signed-cone pullback pattern for
other rank-two return pencils.

### R32-D02: Prime-power ReturnSquare classification

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** graduated

Let `q=pʳ`, where `p` is prime and `r>0`. Then the complete rational parameter classification
is

```text
ReturnSquare(q,c) is mortal  ↔  c=−q⁻ᵐ for some m≥0.
```

The proof normalizes `c=−d`. A return word with scale product `T` produces an integral bridge
polynomial whose constant coefficient is `T` and whose leading coefficient is `±T²`. The
rational-root theorem therefore forces a positive root `d` to be a power of `p` or its
reciprocal. Positive powers lie beyond `R32-D01`. A reciprocal `p⁻ᵏ` is a one-return resonance
when `r∣k`; otherwise a finite quotient preserves one or two nonzero projective rays and
certifies immortality.

The quotient supply is complete. The corpus proves Bang–Zsigmondy for every base `a>1` and
exponent `n>2`, with sole exception `(a,n)=(2,6)`. The exceptional pair is separated by
primitive factors of orders two and three. Exponent two uses a signed two-ray quotient.

**Scope:** the matrix classification requires a prime-power base. A ReturnSquare base with at
least two distinct prime factors can have rational roots supported on several primes and is not
classified here. The general Bang–Zsigmondy theorem is arithmetic infrastructure, not a
decision theorem for arbitrary return pencils.

**Artifact:** `exists_primitivePrimeDivisor`,
`ReturnSquare.physical_isMortal_primePower_iff`, and the bridge-polynomial and finite-wall
theorems in [`PrimitiveDivisor.lean`](MatrixMortality/PrimitiveDivisor.lean),
[`PolynomialPencil.lean`](MatrixMortality/PolynomialPencil.lean),
[`ReturnSquarePrimePower.lean`](MatrixMortality/ReturnSquarePrimePower.lean), and
[`ReturnSquareClassification.lean`](MatrixMortality/ReturnSquareClassification.lean).

**Use:** prime-power ReturnSquare is closed. Search multi-prime or genuinely multi-scale
families instead of longer words in this family.

### R32-M01: Generic reverse edge compiler

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

For a projective-incidence instance `G,H∈GL₂(ℚ)`, row `ℓ`, and column `c`, put

```text
α=ℓH⁻¹c,       β=ℓH⁻¹GH⁻¹c.
```

When `αβ≠0`, a rank-one loop `P`, two cross-edges, and one invertible loop can be chosen so that
successive visits to `P` test exactly `ℓWc=0` for `W∈{G,H}*`. The four edges satisfy the
one-line compatibility needed by [`R32-S02`](#r32-s02-two-plane-edge-square), hence assemble
into two rank-two `3 × 3` matrices.

The basis adaptation and arbitrary-path converse are now checked. Every path fractures at the
rank-one loop. Empty bridges evaluate to a nonzero multiple of that loop; every completed
nonempty bridge erases its invisible plane changes to `WH`, where `W∈{G,H}*`; unfinished
exterior blocks remain nonzero products of units. Thus a constrained path vanishes exactly when
one original incidence coefficient vanishes.

**Scope:** the theorem assumes `αβ≠0`. The two exceptional projective positions remain a
many-one preprocessing problem: a finite Turing disjunction appears straightforward, but no
single three-dimensional emitted OR gadget is checked. This record does not assert a full
many-one equivalence between `M₂(3)` and the rank-`(2,2)` profile.

**Artifact:** `ReverseEdge.isMortal_adaptedGenerator_iff` and
`adaptedGenerator_rank` in [`ReverseEdge.lean`](MatrixMortality/ReverseEdge.lean).

**Use:** treat the generic rank-`(2,2)` stratum as inheriting the dimension-two projective hard
core. Work now belongs on exceptional-point genericization or on the flat constrained edge
languages not fractured by a rank-one loop.

**Next:** replace the exceptional finite disjunction by one computable emitted instance, or
state and use its exact oracle strength.
Tracked in
[#11](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/11).

### R32-M02: Finite-quotient sieve

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Every zero-preserving monoid homomorphism sends mortal families to mortal families. Therefore
one finite quotient in which the image family is immortal is a complete no-certificate for the
original family. This includes reduction of integral candidates modulo primes and finite
projective-state quotients.

**Scope:** the theorem is one-sided. Survival modulo every tested modulus is evidence only and
does not imply rational mortality. No local-global completeness theorem is claimed.

**Artifact:** `MatrixMortality.isMortal_map` and
`not_isMortal_of_map_not_isMortal` in
[`MatrixSemigroup.lean`](MatrixMortality/MatrixSemigroup.lean).

**Use:** use exact finite quotients to kill candidate return pencils before symbolic work, and
record any persistent residue automata as conjectural invariants rather than proofs.

**Next:** build a typed finite-quotient census for irreducible cubic and two-prime return
families; promote only invariants that admit an unbounded lifting theorem.

### R32-M03: Two-scale return conversion

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Replacing ReturnSquare's modes `(1,q,q²)` by `(1,p,q)` gives

```text
Rₙ =
  [(c+1)qⁿ−1   pⁿ]
  [c              pⁿ].
```

The zero return remains the internal rank-one separator and every positive return is invertible
for integral `p,q≥2` and `c≠−1`. The complete physical mortality problem is therefore still one
scalar bridge. Projectively, the exact defect identity

```text
Nₙ(z)−qⁿDₙ(z)=(qⁿ−1)(z−pⁿ)
```

verifies the rail `pⁿ↦qⁿ`; the terminal pullback tests `cqⁿz+pⁿ=0`. A nonsingular coefficient
Hankel section proves that this return series genuinely needs three states when
`p,q,1` are distinct and `c≠−1`.

Unlike ReturnSquare, this pencil has nonresonant multi-return zeros. At
`p=3`, `q=6`, `c=−1/9`, the integral physical pair satisfies

```text
B² A B A² B² = 0,
```

while both central positive returns are invertible and `−1/9` is not a one-return resonance.

**Scope:** one explicit nonresonant zero is not a computation. No self-verifying configuration
set, illegal-wait trap, or undecidability reduction is claimed.

**Artifact:** `ReturnConvert.physical_isMortal_iff_positiveBridge`,
`three_le_card_of_exact_realization`, `projective_rail`, `projective_target_defect`,
`example_zero`, and `example_nonresonant` in
[`ReturnConvert.lean`](MatrixMortality/ReturnConvert.lean).

**Use:** this is the preferred constructive `M₃(2)` laboratory. Seek a valuation-coded legal
rail whose wrong waits enter a permanent trap; test finite quotients before expanding the
architecture.

**Next:** classify the semigroup generated by the projective returns at multiplicatively
independent scales, or exhibit a guarded arithmetic simulation with an all-waits converse.
Tracked in
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-M04: Amalgamated valuation guard

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

For a prime `p`, depth `s≥2`, center `α`, and reset `ρ`, put `δ=ρ−α`. The split
three-mode return family has ambient action

```text
A = diag(1,p⁻¹,p^(s−1))
```

and exact rescaled returns

```text
Gₙ =
  [α+δpˢⁿ    −αpⁿ−δpˢⁿ]
  [1                    −pⁿ].
```

The zero return is the nonnilpotent rank-one outer product
`(ρ,1)ᵀ(1,−1)`; every positive return is invertible. The physical cut has rank exactly two,
the coefficient Hankel certificate has rank three, and the existing split-return compiler
reduces every arbitrary physical zero word to one scalar bridge.

Assume `α`, `α−1`, and `δ` are p-adic units and `ρ` has positive valuation. On `ℙ¹(ℚ)`, the
positive return obeys the cross-multiplied verifier

```text
Φₙ(z)−α = δpˢⁿ(z−1)/(z−pⁿ).
```

Every nonterminal point outside the positive-valuation region forms a forward-invariant trap.
For a live point `z`, surviving a selected wait `n` forces both

```text
n = vₚ(z),                  vₚ(z−pⁿ)=sn.
```

Thus independently selected wrong waits are permanently poisoned without another state or
generator.

**Scope:** this is not an undecidability theorem. It converts physical mortality exactly into
target reachability for one deterministic rational p-adic map. No source computation has yet
been compiled into that map, and no decision algorithm for its orbit is known.

**Artifact:** `ReturnGuard.physical_isMortal_iff_positiveBridge`,
`ReturnGuard.trap_forward`, `live_step_forces_ready`,
`parameters_three_le_card_of_exact_realization`, and the exact integer example
`ReturnGuard.Examples.integer_zero_word` in
[`ReturnGuard.lean`](MatrixMortality/ReturnGuard.lean),
[`ReturnGuardDynamics.lean`](MatrixMortality/ReturnGuardDynamics.lean), and
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean).

**Use:** the separator-verifier-trap amalgamation problem is closed. Future attacks should work
on the deterministic tail recurrence, not add parser states or repair malformed wait words.

**Next:** classify or universalize the guarded arithmetic orbit in
[`R32-S04`](#r32-s04-guarded-return-normal-form).
Tracked in
[#12](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/12).

### R32-S04: Guarded return normal form

**Kind:** structural normal form
**Evidence:** formalized
**Disposition:** active

Write a ready point uniquely as

```text
E(a,X)=pᵃ+pˢᵃ/X,            vₚ(X)=0.
```

The sole legal wait is `a`, and its payload update is

```text
E(a,X) ↦ α+(ρ−α)(pˢᵃ+(pᵃ−1)X).
```

Every positive ready cylinder can reach every other: the inverse unit tail is an explicit
fractional-linear expression. The terminal tail is likewise explicit and unique. Nevertheless,
all arbitrary physical paths are already covered. Lean proves

```text
physical mortality
  ↔ some positive-return projective word reaches 1
  ↔ TransGen LegalStep ρ 1.
```

The last relation is functional. Its proof reads physical matrix products in their actual
right-to-left action order, propagates trap invariance through every suffix, and forces every
surviving step to be ready. The construction therefore has neither an intended-word loophole
nor a hidden regular-language restriction.

**Scope:** the complete inverse grammar shows local symbolic freedom, not computational
universality. The rational tail couples successive cylinder choices globally.

**Artifact:** `readyTail_isUnit`, `readyState_readyTail`, `readyState_ready`,
`ready_transition`, `legalValue_eq_one_iff`, `legalStep_functional`, and
`physical_isMortal_iff_guardedReachable` in
[`ReturnGuardDynamics.lean`](MatrixMortality/ReturnGuardDynamics.lean).

**Use:** formulate the surviving `M₃(2)` attack entirely as reachability for this deterministic
arithmetic system. Matrix rank, punctuation, malformed words, illegal waits, and exact
three-state minimality no longer belong to the open obligation.

**Next:** either reduce a universal deterministic computation to `GuardedReachable`, or find a
finite-height, p-adic contraction, or continued-fraction invariant deciding it.

### R32-S05: Prefix shift and affine residual

**Kind:** structural normal form
**Evidence:** formalized
**Disposition:** active

In the shifted projective coordinate

```text
x=z/(z−1),
```

one legal guard step factors into a variable-length affine prefix decoder and one fixed
fractional-linear map:

```text
Dₐ(x) = (pᵃ+(1−pᵃ)x)/pˢᵃ,
K(w)  = (αw+δ)/((α−1)w+δ),
x'    = K(Dₐ(x)).
```

Readiness is exactly the assertion that `Dₐ(x)` is a p-adic unit. Parameterizing one branch by

```text
Φₐ(v)=(pˢᵃv−δ)/(α−pᵃ)
```

turns the reciprocal residual update into

```text
1/Rₐ(Φₐ(v))
  = [δ(1−pᵃ)/(α−pᵃ)] · 1/v
    + [(α−1)pˢᵃ/(α−pᵃ)].
```

The Lean statements retain every required denominator hypothesis. The shift identity itself
uses total rational division at a terminal output; it is interpreted projectively only away
from the input target and pole.

**Scope:** affine residual transport can propagate unbounded carries, but it does not provide a
finite-token compiler or a decision procedure.

**Artifact:** `ReturnGuard.shift_step`, `ready_iff_prefixDecode_isUnit`,
`residualStep_branchCylinder`, and `reciprocalResidual_affine` in
[`ReturnGuardShift.lean`](MatrixMortality/ReturnGuardShift.lean).

**Use:** work on the arithmetic residue as a prefix/carry transducer. Any proposed finite-token
simulation must still evade the closed-substitution collapse.

**Next:** classify the iterated affine residuals on the resonant cylinders isolated by
[`R32-S06`](#r32-s06-resonance-localization).

### R32-S06: Resonance localization

**Kind:** structural normal form
**Evidence:** formalized
**Disposition:** active

Let `u=α/δ`, and write a unit tail at exact depth `n` as

```text
X=u+pⁿY,                  vₚ(Y)=0.
```

For a current wait `a`, the three summands of the legal output have valuations `a`, `sa`, and
`n`. Lean proves the complete trichotomy:

```text
n<a  ⇒ every ready continuation has next wait n<a;
n>a  ⇒ the output is not ready, and every further positive step lies in the trap;
n=a  ⇒ the sole branch on which the wait can be preserved or increased.
```

The exact center `X=u` also admits no ready continuation. Consequently every infinite ready
chain meets the equal-depth resonance shell arbitrarily far along the chain; otherwise its
positive waits would descend forever in `ℕ`.

At resonance the output factors as `pᵃ C`. If `C=pʰU` with `U` a unit, readiness at the next
wait `a+h` is equivalent to

```text
vₚ(U−1)=(s−1)(a+h).
```

This corrects the reported depth `(s−1)a+sh`, which was too large by `h`.

**Scope:** resonance localization does not classify the resonant itinerary. It proves that all
nondecreasing or infinite behavior is confined to the nested equal-depth shell.

**Artifact:** `ReturnGuard.nonresonant_nextWait_lt`,
`infinite_ready_chain_resonates`, `primePower_mul_ready_iff`, and
`resonance_ready_iff` in
[`ReturnGuardResonance.lean`](MatrixMortality/ReturnGuardResonance.lean).

**Use:** discard generic unit tails. Universality or decidability must be proved inside the
iterated resonance carry.

**Next:** seek an effective nucleus or nonperiodic rational itinerary for the nested normalized
residual.

### R32-O06: Rational affine-wait rail rigidity

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let a reduced rational chart be `f=P/Q`, with `P,Q∈ℚ[X]`, `P(0)≠0`, and let the proposed wait
update be

```text
a ↦ da+h,                 t=pᵃ ↦ λtᵈ,   λ=pʰ.
```

If the guarded rail equation holds at infinitely many defined prime-power samples, clearing
denominators gives one polynomial identity. The formal proof extracts the stronger divisibility

```text
P(λXᵈ) ∣ Q(X).
```

Degree comparison first forces `d=1` and `deg P=deg Q`. Constant and leading coefficients then
force

```text
α=λ^(s+deg P).
```

Since `α` is a p-adic unit, this contradicts `vₚ(λ)≠0`. Thus no rational ready-tail chart can
implement a nontrivial affine change of wait on infinitely many configurations. The intermediate
degree theorem already excludes every `d>1` for any nonzero `λ`.

This proof is shorter and stronger than the reported algebraic-closure root count: reducedness
and polynomial divisibility suffice.

**Scope:** the theorem concerns one reduced rational chart. A finite-control cycle is excluded
only after its charts are shown to compose to this rail equation; that compiler-level corollary
is not represented as a Lean type. Identity-wait charts and genuinely nonrational nested
resonance remain possible.

**Artifact:** `ReturnGuard.Rail.scalePower_numerator_dvd_denominator`,
`identity_forces_linear_center`, `no_rational_affineWait_rail`, and
`no_infinite_primePower_affineWait_rail` in
[`ReturnGuardRail.lean`](MatrixMortality/ReturnGuardRail.lean).

**Use:** abandon rational monomial counter rails, rational increment/decrement gauges, and
rational affine counter cycles. The live construction must use the nested resonance itself.

**Next:** decide whether rational resonant itineraries have an effective eventual-periodicity
theorem, or construct a rational nonperiodic resonance stack.

### R32-S07: Decoded residual address normal form

**Kind:** structural normal form
**Evidence:** formalized
**Disposition:** active

The reciprocal center displacement

```text
w = (ρ−α)/(z−α),             z = α+(ρ−α)/w
```

is the canonical global state. Reset is `w=1`; the terminal point is
`τ=−(ρ−α)/(α−1)`. For every positive wait `a`, the exact legal domain is one rational p-adic
sphere

```text
Bₐ = βₐ+pˢᵃ ℤₚ×,            βₐ=−(ρ−α)/(α−pᵃ).
```

On rational points the inverse branch

```text
gₐ(v) =
  (ρ−α)(pˢᵃv−1) /
  (α−pᵃ−(α−1)pˢᵃv)
```

maps the rational unit shell bijectively onto `Bₐ`. The spheres are pairwise disjoint, so the
state itself determines the wait. Lean transports every original legal step through this
coordinate and proves

```text
physical mortality
  ↔ ∃ nonempty positive address (a₀,…,aₙ), 1=gₐ₀∘⋯∘gₐₙ(τ).
```

Distinct positive branches have no common finite fixed point. Hence their nonlinear interaction
cannot be removed by choosing one finite affine chart. The exact rational period-three orbit

```text
1 ─1→ 5/17 ─2→ 43/283 ─3→ 1
```

is also checked. Its first two legs are equal-depth resonances and its third is a strict
nonresonant descent. Rational survival is therefore not confined to fixed points or two-cycles.

**Scope:** the Lean theorem is rational and exact. It does not claim a topological conjugacy on
all of `ℚₚ`, nor eventual periodicity of rational addresses.

**Artifact:** `ReturnGuard.residualEquiv`,
`residualBranch_iff_exists_inverseResidual`,
`residualBranch_wait_unique`, `guardedReachable_iff_decodedReachable`,
`physical_isMortal_iff_inverseAddress`, `residualFixed_exclusive`,
`ReturnGuard.Examples.cycle_decoded_orbit`, and `cycle_first_two_resonant` in
[`ReturnGuardGauss.lean`](MatrixMortality/ReturnGuardGauss.lean),
[`ReturnGuardAddress.lean`](MatrixMortality/ReturnGuardAddress.lean), and
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean).

**Use:** replace the wait-tail bookkeeping by one countably branched Möbius system. The remaining
decision question is finite inverse-address membership of one rational point, not legality of
arbitrary physical words.

**Next:** attack rational address arithmetic with the local-global sieve in
[`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve), or exhibit a rational
non-eventually-periodic address carrying universal computation.

### R32-M05: Cyclotomic reset-or-cancellation sieve

**Kind:** partial mechanism
**Evidence:** formalized
**Disposition:** active

Write `α=A/L`, `ρ−α=D/L`, and a primitive decoded residual as `m/n`. One surviving wait `a`
has the exact integral recurrence

```text
pˢᵃ m̃ = (A−Lpᵃ)m+Dn,
ñ      = (A−L)m+Dn.
```

Lean proves that projectivizing `(m̃,ñ)` recovers the decoded residual map exactly. More
generally, a common divisor of the image of any primitive pair under a `2 × 2` integer matrix
divides its determinant. Applied here, every common reduction factor `g` coprime to `p` satisfies

```text
g ∣ DL(pᵃ−1).
```

If a prime `ℓ` divides `pᵃ−1`, then one exact dichotomy holds after primitive reduction:

```text
ℓ ∣ g
  or
m′ ≡ n′ (mod ℓ).
```

Thus every cyclotomic prime either disappears into a visible common cancellation or resets the
reduced projective point to one. There is no third escape.

The cancellation branch itself is now exact. For every positive wait and every divisor
`d ∣ pᵃ−1`, primality is unnecessary: `d` is automatically coprime to `p`. If

```text
(m̃,ñ)=g(m′,n′),    gcd(m′,n′)=1,
```

then Lean proves

```text
d ∣ g
  ↔
(A−L)m ≡ −Dn (mod d).
```

The right side is precisely projective congruence of the source residual `m/n` with the terminal
residual `−D/(A−L)`. A swallowed cyclotomic factor is therefore not an opaque failure of
reduction: the source state already shadows the terminal divisor modulo that entire factor.

**Scope:** this is a one-step local-global theorem, not a decision algorithm. Terminal
congruence may recur at unbounded orders, and no bound on the accumulated cyclotomic factors or
the terminal defect is yet proved.

**Artifact:** `ReturnGuard.integralStep_realizes_residualStep`,
`commonDivisor_dvd_det`, `integralStep_commonDivisor_dvd_cyclotomicSupport`, and
`integralStep_cyclotomic_reset_or_cancel`, together with the stronger
`divisor_pow_sub_one_isCoprime_base` and
`integralStep_cyclotomic_cancel_iff_terminalCongruent`, in
[`ReturnGuardArithmetic.lean`](MatrixMortality/ReturnGuardArithmetic.lean).

**Use:** finite quotients should track a projective residue plus an explicit cancellation state.
An unreachable terminal residue certifies immortality. Reaching the cancellation state now
certifies terminal congruence upstairs and charges the swallowed factor to the integral terminal
defect.

**Next:** track primitive parts of `pᵃ−1` against the height of the terminal defect, or prove that
the resulting terminal-congruence histories form an effective finite nucleus.

### R32-S08: Terminal-defect cocycle

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

The terminal defect

```text
T(m,n)=(A−L)m+Dn
```

is exactly the next denominator before primitive reduction. In coordinates `(m,T)`, one integral
step obeys

```text
pˢᵃ m̃ = T + L(1−pᵃ)m,
pˢᵃ T(m̃,ñ)
  = (A−L+Dpˢᵃ)T + (A−L)L(1−pᵃ)m.
```

If the raw output reduces by `g` to `(m₁,n₁)` and the following terminal defect reduces by
`h` to `n₂`, Lean eliminates the numerator and obtains the exact second-order recurrence

```text
g pˢᵃ h n₂
  = g(A−Lpᵃ+Dpˢᵃ)n₁ − DL(1−pᵃ)n₀.
```

The fixed parameter support must be separated from novel cyclotomic cancellation. For every
modulus `d` coprime to `pDL`,

```text
d ∣ g
  ↔
d ∣ pᵃ−1
  and
(A−L)m ≡ −Dn (mod d).
```

This is the exact outside-support cancellation law.

The checked rational period-three survivor makes the distinction necessary. Its three primitive
reduction factors are

```text
160, 28, 3440,
```

and each divides the fixed product `DL=473·2240`. Its height grows from denominator `1` through
`17` and `283`, then collapses to `1` without swallowing any novel cyclotomic prime. No theorem
based on monotonicity of total height or total common cancellation can therefore work.

**Scope:** the cocycle and recurrence are exact, but they do not bound the fixed-prime valuations
or the outside-support cyclotomic part. The example disproves a naïve total-height argument; it
does not disprove a height on the quotient by fixed `S`-unit normalization.

**Artifact:** `ReturnGuard.integralStep_terminalDefect`,
`reducedDenominator_recurrence`,
`integralStep_novel_cancel_iff_cyclotomic_terminalCongruent`, and
`ReturnGuard.Examples.cycle_commonFactors_dvd_fixedSupport` in
[`ReturnGuardCocycle.lean`](MatrixMortality/ReturnGuardCocycle.lean),
[`ReturnGuardArithmetic.lean`](MatrixMortality/ReturnGuardArithmetic.lean), and
[`ReturnGuardExamples.lean`](MatrixMortality/ReturnGuardExamples.lean).

**Use:** organize the decision attack as an `S`-arithmetic problem. Primes dividing `DL` own the
normalization state; outside that fixed set, every cancellation factor simultaneously lies in
`pᵃ−1` and the terminal defect.

**Next:** define the fixed-support-free part of an integer, derive its transport through the
denominator recurrence, and test whether it has an effective finite nucleus.

### R32-S09: Complete cancellation law

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let one integral step send a source pair `(m,n)` to a raw pair `(m̃,ñ)`, and write

```text
(m̃,ñ)=g(m′,n′),    gcd(m′,n′)=1.
```

For every integer divisor `d` coprime to the base `p`, Lean proves the exact equivalence

```text
d ∣ g
  ↔
d ∣ T(m,n)
  and
d ∣ L(1−pᵃ)m,
```

where `T(m,n)=(A−L)m+Dn` is the terminal defect. The theorem contains both previously separated
mechanisms:

- if `d ∣ pᵃ−1`, the displacement condition is automatic and cancellation is terminal
  congruence;
- if `d` lies in the fixed support of `L` or the source numerator `m`, cancellation need not be
  cyclotomic, but it is still charged to the same terminal defect.

Prime-power divisibility makes the local multiplicities exact. For every prime `ℓ≠p`, assuming
the three relevant integers are nonzero,

```text
vℓ(g)=min(vℓ(T(m,n)), vℓ(L(1−pᵃ)m)).
```

No further common-factor mechanism exists away from the base prime. In particular, the
determinant-support theorem is a consequence-level bound; the intersection law is the local
normal form.

**Scope:** the exact displacement valuation contains `vℓ(m)`, but this does not survive as an
unbounded size contribution on primitive legal states. The determinant-support theorem bounds
the attained cancellation by `vℓ(DL(pᵃ−1))`; [`R32-S10`](#r32-s10-logarithmic-wait-and-height-envelope)
records the resulting logarithmic law. The source valuation still decides whether the bound is
attained.

**Artifact:** `ReturnGuard.integralStep_cancel_iff_terminalDefect_and_displacement` and
`ReturnGuard.integralStep_commonFactor_padicValInt` in
[`ReturnGuardArithmetic.lean`](MatrixMortality/ReturnGuardArithmetic.lean).

**Use:** replace every coarse gcd estimate by a prime-local equality. Outside fixed support this
recovers cyclotomic terminal shadowing; inside fixed support it isolates the exact valuation
state that a normalization quotient must retain.

**Next:** combine the exact attainment condition with the global logarithmic height envelope.
The unresolved state is terminal congruence, not the magnitude of fixed-prime cancellation.

### R32-S10: Logarithmic wait and height envelope

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a primitive integral source pair of height

```text
H(m,n)=max(|m|,|n|),
```

every base-coprime primitive-reduction factor satisfies

```text
|g| ≤ |DL| |pᵃ−1|.
```

Prime locally,

```text
vℓ(g) ≤ vℓ(D)+vℓ(L)+vℓ(pᵃ−1).
```

Thus the source term in the complete displacement formula affects attainment but not size. For
an odd fixed prime `ℓ`, if `r` is any seed period with `ℓ ∣ pʳ−1`, lifting the exponent gives

```text
vℓ(p^(rk)−1)=vℓ(pʳ−1)+vℓ(k)
            ≤vℓ(pʳ−1)+logℓ(k).
```

Lean proves the corresponding logarithmic bound at `ℓ=2`, separating odd and even multipliers
through the two-adic lifting formula.

The same integral recurrence has a uniform archimedean envelope. If the depth `s≥2` and the next
numerator is nonzero, then

```text
a ≤ log_p((|A|+|D|+|L|)H(m,n)).
```

Before and after primitive reduction,

```text
H(m′,n′) ≤ (|A|+|D|+|L|)H(m,n).
```

The wait therefore grows at most logarithmically in current height, while height grows by at
most one fixed factor per transition. Along an orbit, waits can grow at most linearly in elapsed
steps.

**Scope:** this is not a finite nucleus. Linear wait growth and exponential height growth remain
ample enough for counter-like computation. The theorems bound cancellation and scale but do not
decide the terminal congruences that select a rational inverse address.

**Artifact:** `ReturnGuard.integralStep_commonFactor_padicValInt_le_support`,
`integralStep_commonFactor_natAbs_le_support`, `padicValNat_pow_mul_sub_one_le`,
`padicValNat_two_pow_mul_sub_one_le`, `integralStep_wait_le_log_height`, and
`integralStep_reduced_height_le` in
[`ReturnGuardValuation.lean`](MatrixMortality/ReturnGuardValuation.lean).

**Use:** exclude any universality proposal requiring one step to generate a superlinear clock or
super-Lipschitz rational height. For a decision proof, combine the envelope with terminal-defect
congruence to seek a finite set of recurrent projective residues.

**Next:** derive an iterated terminal-defect height or finite-quotient recurrence that uses the
linear wait bound. Conversely, construct a legal rational orbit whose terminal congruences
saturate that envelope and encode an unbounded counter.

### R32-S11: Primitive-factor terminal gate

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For one legal integral step, let `g` be the primitive-reduction factor and let `T` be the source
terminal defect. Given any finite family `S` of distinct cyclotomic primes dividing `pᵃ−1`,
Lean combines pairwise coprimality with the reset-or-cancellation theorem to prove

```text
|T| < ∏_{ℓ∈S} ℓ
  ⇒
T=0
  or
∃ℓ∈S, ℓ∤g and m′≡n′ (mod ℓ).
```

Thus a family whose squarefree product is larger than the terminal defect cannot disappear
silently. Either the source is already the true terminal projective point, or one factor
survives primitive reduction and resets the reduced state to one in a finite projective
quotient.

The canonical family consists of the prime factors of `Φ_a(p)` which do not divide `a`. Every
such factor is formally proved to be a primitive prime divisor of `pᵃ−1`. Writing

```text
radₚᵣᵢₘ(Φ_a(p)) = ∏ {ℓ : ℓ∣Φ_a(p), ℓ∤a},
```

the checked height form is

```text
radₚᵣᵢₘ(Φ_a(p)) >
  (|A−L|+|D|)H(m,n)
⇒
T(m,n)=0
or
some exact-order quotient sees m′≡n′.
```

Equivalently, on a nonterminal step for which every primitive quotient reset is ruled out,

```text
radₚᵣᵢₘ(Φ_a(p))
  ≤ |T(m,n)|
  ≤ (|A−L|+|D|)H(m,n).
```

This is the precise local-global gate sought by [`R32-M05`](#r32-m05-cyclotomic-reset-or-cancellation-sieve).
It replaces the vague requirement that “cyclotomic growth beat height” by a squarefree radical
inequality and exposes exactly where pure size arguments stop.

**Scope:** no unconditional lower bound strong enough for the primitive cyclotomic radical is
proved. Cyclotomic values grow like `p^φ(a)`, but repeated prime powers can make their
squarefree radical much smaller; controlling that loss uniformly is a genuinely number-theoretic
obligation. Nor does a surviving reset automatically reject the terminal residue: it supplies a
finite exact-order quotient whose future reachability must still be analyzed.

**Artifact:** `primitiveCyclotomicPrimes`,
`primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes`,
`terminal_or_exists_cyclotomic_reset`,
`cyclotomicProduct_le_terminalDefect_of_no_reset`,
`terminalDefect_zero_or_exists_primitive_reset`, and
`primitiveCyclotomicRadical_le_height_of_no_reset` in
[`ReturnGuardTerminalGate.lean`](MatrixMortality/ReturnGuardTerminalGate.lean).

**Use:** split the remaining decision attack cleanly. A surviving primitive factor enters a
finite projective graph of exact multiplicative order `a`; if every such graph is inconclusive,
the primitive radical is charged to one explicit terminal defect and bounded by primitive
height.

**Next:** prove either that enough primitive factors survive to yield a complete finite-quotient
certificate, or that repeated failure forces a radical-divisibility history belonging to a
known hard Diophantine class. A bare lower bound for `Φ_a(p)` is insufficient; the needed object
is its primitive squarefree part.

### R32-S12: Exact-order projective automata

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Let `ℓ` be a primitive prime divisor of `pᵉ−1`. Clearing denominators in the decoded residual
recurrence gives one homogeneous `2 × 2` transfer matrix. Modulo `ℓ`, every entry depends only
on the wait modulo `e`; projectivization therefore produces a finite automaton on

```text
ℙ¹(𝔽ℓ) ⊔ {cancelled}.
```

The extra state is exact arithmetic, not an overapproximation. For every primitively reduced
integral step, the quotient enters `cancelled` if and only if `ℓ` divides the common reduction
factor. Otherwise it follows the reduced projective point exactly. Consequently, any finite set
of quotient states which contains the reset, is closed under all `e` residue transitions, and
contains neither `cancelled` nor the terminal ray is a kernel-checked certificate excluding
every primitive integral terminal execution.

There is a uniform rank-one subfamily. If additionally `ℓ∣D`, every transfer loses its second
column. Assume `A−L` is nonzero modulo `ℓ` and

```text
A−Lpʳ ≠ 0  for every 0≤r<e.
```

Then every residue transition sends every nonzero affine ray to another nonzero affine ray,
while the terminal residual `−D/(A−L)` becomes zero. The entire nonzero affine shell is a safe
invariant, yielding an immediate no-certificate. Equivalently, the center ratio `A/L` must avoid
the cyclic subgroup generated by `p`.

For the rational period-three survivor with parameters

```text
p=3, s=2, A=−953, D=473, L=2240,
```

the primitive quotient `ℓ=11`, of exact order five, collapses all five residue transfers onto
the four affine rays `{1,4,6,10}`. This set is closed, while the terminal ray is `0` and
`cancelled` is absent. Lean therefore excludes every primitive integral execution from reset
pair `(1,1)` to terminal pair `(−473,−3193)`, not merely the displayed period-three orbit.
Independently, determinism of the decoded relation and the same three-state rational invariant
prove that the corresponding physical matrix pair is immortal.

**Scope:** this proves a finite certificate language, not its completeness. Many primitive
quotients are saturated and admit both terminal and cancellation paths. The concrete
modulo-eleven collapse is unusually strong because `11∣D`, making every residue transfer rank
one with zero second column. [`R32-S13`](#r32-s13-canonical-decoded-integral-lift) now supplies
the formerly missing bridge from every decoded rational execution to primitive integral
execution. Quotient invariants are therefore physical immortality certificates, but no theorem
asserts that every immortal parameter set admits one.

**Artifact:** `ReturnGuard.quotientTransfer_mod_of_primitive`,
`quotientTransition_integralStep_eq_cancelled_iff`,
`no_primitiveExecution_of_quotientInvariant`,
`no_primitiveExecution_of_drift_divisor`, and
`ReturnGuard.Examples.cycle_no_primitive_integral_terminal_execution` in
[`ReturnGuardQuotient.lean`](MatrixMortality/ReturnGuardQuotient.lean) and
[`ReturnGuardQuotientExamples.lean`](MatrixMortality/ReturnGuardQuotientExamples.lean).

**Use:** search exact-order finite quotients for a closed safe invariant. A successful invariant
is a proof object with a finite transition table; failure identifies whether the escape is
terminal reachability or actual cyclotomic swallowing.

**Next:** separate the special rank-one quotients arising from parameter divisors from genuinely
projective exact-order certificates, and test whether either family is complete.

### R32-S13: Canonical decoded-integral lift

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

For a rational residual `w`, let

```text
pair(w)=(num(w),den(w))
```

be its canonical reduced integer pair. Suppose the guarded coefficients have a common integral
presentation

```text
α=A/L,        ρ−α=D/L,        L≠0.
```

On a legal decoded branch of wait `a`, direct denominator clearing gives

```text
S_a(w)=N / (p^(sa)T),
N=(A−Lpᵃ)num(w)+D den(w),
T=(A−L)num(w)+D den(w).
```

The target is a p-adic unit. Its canonical denominator is therefore prime to `p`. When raw
fraction reduction writes

```text
N=c·num(S_a(w)),
p^(sa)T=c·den(S_a(w)),
```

Euclid's lemma forces `p^(sa)∣c`. Removing that forced power yields exactly the integer
recurrence `PrimitiveIntegralStep`; both source and target pairs are primitive by rational
normalization. This construction is canonical and transports every exact decoded execution
step for step without changing its length.

Consequently, a closed exact-order quotient invariant containing the canonical reset pair and
excluding both cancellation and the canonical terminal pair proves decoded unreachability and
hence physical immortality. The drift-divisor subfamily needs no coprimality assumption on the
chosen coefficients: the raw terminal pair and its canonical reduction represent the same
finite projective point whenever `A−L` survives the quotient.

**Scope:** the lift is one-way because that is the soundness direction needed by finite
no-certificates. It does not say that every abstract `PrimitiveIntegralStep` is a legal decoded
step, nor that the finite quotient family is complete.

**Artifact:** `ReturnGuard.rationalPair`,
`rat_denominator_not_dvd_of_isUnit`,
`decodedStep_primitiveIntegralStep`,
`decodedExecution_primitiveIntegral`,
`not_physical_isMortal_of_quotientInvariant`, and
`not_physical_isMortal_of_drift_divisor` in
[`ReturnGuardIntegralLift.lean`](MatrixMortality/ReturnGuardIntegralLift.lean);
`ReturnGuard.Examples.cycle_not_physical_isMortal_by_quotient` in
[`ReturnGuardQuotientExamples.lean`](MatrixMortality/ReturnGuardQuotientExamples.lean).

**Use:** every quotient invariant may now be read literally as a finite certificate about the
physical matrix pair. Search and classification can operate on finite projective automata
without reopening rational-normalization soundness.

**Next:** characterize which guarded parameters possess a drift-divisor certificate; then seek
generic primitive quotients for the complement and determine whether repeated cancellation
forces an effectively recognizable arithmetic history.

### R32-S14: Drift-divisor certificate classification

**Kind:** decidable stratum
**Evidence:** formalized
**Disposition:** active

Fix a primitive divisor `ℓ` of `pᵉ−1` and assume `ℓ∣D`. The residual transfer modulo `ℓ` has
only its first column. Define the scaled center orbit

```text
O={L pʳ : 0≤r<e}⊆𝔽ℓ.
```

Then the following are equivalent:

1. some quotient invariant contains the reset and excludes both annihilation and the terminal
   ray;
2. the nonzero affine survivor shell is such an invariant;
3. `A∉O`;
4. when `A` and `L` survive, `A/L∉⟨p⟩⊆𝔽ℓ×`;
5. the executable Boolean classifier `driftDivisorCertifies` returns true.

The necessity is stronger than the earlier construction. If `A=Lpʳ`, closure from the reset
under residue `r` reaches either annihilation, when the first column vanishes, or the terminal
zero ray. Hence no alternative smaller invariant can repair a failed orbit test.

The primitive-divisor hypothesis gives multiplicative order exactly `e`, with `e∣ℓ−1`. If
`L≠0` modulo `ℓ`, the orbit has exactly `e` elements. Precisely `ℓ−e` center residues therefore
admit drift-divisor certificates. This quantifies the stratum: a large factor of small order
certifies most center classes, while a primitive-root factor (`e=ℓ−1`) certifies only the zero
class.

**Scope:** this classifies every safe invariant for quotients which divide `D`; it says nothing
about primitive quotients with nonzero drift, combinations of several quotient factors, or
completeness of the whole finite-quotient method. Failure of the Boolean test means that this
one drift-divisor quotient cannot certify immortality, not that the physical pair is mortal.

**Artifact:** `IsPrimitivePrimeDivisor.unit_orderOf_eq_exponent`,
`IsPrimitivePrimeDivisor.exponent_dvd_prime_sub_one`,
`ReturnGuard.affineSurvivors_quotientInvariant_iff_centerPowerOrbit_avoids`,
`hasQuotientCertificate_iff_centerPowerOrbit_avoids`,
`mem_centerPowerOrbit_iff_centerRatio_mem_zpowers`,
`card_centerPowerOrbit`, `card_certifyingCenters`,
`hasQuotientCertificate_iff_driftDivisorCertifies`, and
`not_physical_isMortal_of_driftDivisorCertifies` in
[`PrimitiveDivisor.lean`](MatrixMortality/PrimitiveDivisor.lean) and
[`ReturnGuardDriftCertificate.lean`](MatrixMortality/ReturnGuardDriftCertificate.lean).

**Use:** factor the nonzero drift numerator in a fixed integral presentation, test each primitive
factor once, and discard the entire parameter set as immortal as soon as one factor accepts.
Search effort on failed factors is now provably wasted; the next quotient must have nonzero
drift.

**Next:** study generic exact-order quotients with nonzero drift. By
[`R32-S15`](#r32-s15-finite-quotient-completeness), ordinary synchronized products cannot
strengthen a failed factor; any further local-global method must retain information across
primitive cancellation.

### R32-S15: Finite-quotient completeness

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

For integral residual parameters `(A,D,L)`, the zero-wait quotient transfer is

```text
⎡ A−L  D ⎤
⎣ A−L  D ⎦.
```

Its projective kernel is the terminal residual `τ=−D/(A−L)`. The canonical primitive integer
pair of `τ` is therefore sent to the absorbing cancellation state by residue zero in every
prime quotient. It follows that any transition-closed set containing the terminal already
contains cancellation.

Consequently the following are equivalent for every exact-order quotient:

1. a safe invariant contains reset and excludes cancellation and terminality;
2. a cancellation-free invariant contains reset;
3. cancellation is unreachable from reset in the finite quotient automaton.

The target-absence premise in the earlier certificate interface was redundant. A
cancellation-free invariant alone is a physical immortality certificate through the canonical
decoded-integral lift.

This also closes the obvious multi-prime composition. A synchronized two-factor invariant must
exclude cancellation in each coordinate. Projecting it onto either coordinate yields a
single-factor cancellation-free invariant, because every raw wait remains available after
projection. Hence a synchronized product cannot certify any instance missed by either
component; it is strictly no stronger than its projections.

**Scope:** this obstruction applies to products which track ordinary prime projective states
and reject any swallowed factor. It does not exclude an enriched local state which records the
factor's cancellation exponent and resumes after primitive renormalization, nor a composite
ring model retaining such valuation data.

**Artifact:** `ReturnGuard.quotientTransition_zero_terminal_eq_cancelled`,
`terminal_mem_forces_cancelled`,
`hasQuotientCertificate_iff_hasCancellationFreeInvariant`,
`hasCancellationFreeInvariant_iff_cancelled_unreachable`,
`hasQuotientCertificate_iff_cancelled_unreachable`,
`not_physical_isMortal_of_cancellationFreeQuotient`,
`not_physical_isMortal_of_cancelled_unreachable`,
`hasSynchronizedCancellationFreeInvariant_imp_components`, and
`hasSynchronizedCancellationFreeInvariant_imp_quotientCertificates` in
[`ReturnGuardQuotientCompleteness.lean`](MatrixMortality/ReturnGuardQuotientCompleteness.lean).

**Use:** reduce every ordinary finite-quotient search to one graph question: can any residue
word annihilate the reset ray? Do not build products of cancellation-rejecting automata.

**Next:** enrich the quotient state across swallowed factors. Track the exact valuation removed
by primitive reduction and test whether bounded cancellation memory yields a finite nucleus or
whether unbounded cancellation carries the missing computational stack.

### R32-S16: Cancellation blow-up and unbounded depth

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

Let the two raw output coordinates be encoded by a terminal term

```text
T = ℓᵗT₀
```

and a cyclotomic displacement

```text
P N − T = ℓᵉC₀,
```

where `T₀,C₀` are `ℓ`-adic units. Dividing both coordinates by
`ℓ^min(t,e)` gives an exact strict transform with three exits:

```text
t<e:  [N:T] ≡ [1:1],
e<t:  [N:T] ≡ [1:0],
t=e:  [N:T] ≡ [T₀+C₀:T₀]       (mod ℓ).
```

Thus only equal-depth cancellation retains information. Its tangent parameter is unrestricted:
over every field the exceptional divisor maps surjectively onto `ℙ¹`. The two unequal-depth
charts give one and infinity, while `C₀/T₀` ranges over every remaining affine point. A
swallowed prime can therefore reconstruct *any* quotient state after normalization.

This loss cannot be repaired by choosing a larger fixed modulus. For every truncation depth
`N`, the raw pairs

```text
(ℓᴺ, −ℓᴺ),       (ℓᴺ, ℓᴺ⁺¹)
```

are indistinguishable modulo `ℓᴺ`, but their normalized exits are zero and one. No a priori
fixed congruence jet determines continuation through every collision.

The obstruction occurs inside the actual integral guard recurrence, not merely in an abstract
local model. Any exact factorization

```text
pᵃ−1 = ℓᵈu,       ℓ∤u
```

has a uniform primitive source whose integral step cancels exactly `ℓᵈ`, remains primitive
after division, and exits at zero modulo `ℓ`. Specializing to

```text
(p,s,A,D,L)=(5,2,29,1,1),       a=2·3^(d−1),
```

lifting the exponent gives `v₃(5ᵃ−1)=d`. Hence one fixed recurrence realizes every positive
`3`-adic cancellation depth on primitive inputs.

**Scope:** unboundedness is over the full primitive transition relation. It does not yet prove
that one orbit from the fixed reset realizes unbounded depths. An orbit-specific height theorem
could still yield a finite decision procedure. Nor does the result forbid an algorithm which
carries exact valuations symbolically rather than factoring through a fixed finite congruence
quotient.

**Artifact:** `ReturnGuard.cancellationJet_eq`,
`cancellationJet_terminalDepth_lt_ofPair`,
`cancellationJet_displacementDepth_lt_ofPair`,
`cancellationJet_depth_eq_mod`,
`localCancellationExit_surjective`,
`cancellationExit_escapes_fixed_truncation`,
`primitive_integralStep_of_exact_cyclotomicDepth`,
`exists_primitive_integralStep_with_three_cancellationDepth`, and
`integralStep_cancellationExit` in
[`ReturnGuardCancellationJet.lean`](MatrixMortality/ReturnGuardCancellationJet.lean).

**Use:** abandon uniform fixed-jet quotient nuclei. On the decidability side, prove an
orbit-specific bound on equal-depth tangent collisions or discover a symbolic normalization
whose well-founded measure survives arbitrary depth. On the undecidability side, the equal-depth
tangent is now a concrete unbounded storage channel: force one reset orbit to select its leading
digits recursively.

**Next:** decide whether the canonical reset orbit can realize unbounded cancellation depth.

### R32-S17: Normalized tangent cocycle

**Kind:** structure theorem
**Evidence:** formalized
**Disposition:** active

Primitive cancellation resumes as an exact two-dimensional recurrence. For a reduced pair
`(m,n)` in the chart belonging to a preceding wait `a`, put

```text
P = p^(sa),              v = (n, Pm−n).
```

If the next wait is `b`, define

```text
M(P,b) =
  [ A−L+DP      A−L       ]
  [ L(1−pᵇ)     L(1−pᵇ)   ].
```

For consecutive primitive reductions with next common factor `g`,

```text
M(P,b) v = Pg v′,
```

where `v′` is the tangent pair in the chart `p^(sb)`. This equality retains the complete
normalization scalar. If `(m,n)` is primitive and `n` is coprime to `P`, then `v` is primitive
as well.

The determinant is

```text
det M(P,b) = DLP(1−pᵇ).
```

Hence the blow-up is recursive. Away from fixed parameter primes and the preceding `p`-power,
every new tangent cancellation factor again divides `pᵇ−1`. Modulo such a cyclotomic prime the
matrix has one explicit kernel line:

```text
(A−L+DP)T + (A−L)C = 0.
```

An ensuing swallowed factor is exactly passage of the normalized tangent `(T,C)` through this
line. Primitive normalization has not converted the problem into a finite correction; it has
recreated the same fixed-versus-cyclotomic cancellation dichotomy on the exceptional divisor.

There is no unconditional scalar descent on this cocycle. The checked canonical period-three
guard carries the exact nonzero projective tangent cycle

```text
(17,28) → (283,3200) → (1,728) → (17,28),
```

with normalization scalars `−252`, `−278640`, and `−116640`. Every ordinary normalization
factor in this example lies in fixed parameter support, so the cycle does not refute an
orbit-specific bound on *novel* tangent depth. It does prove that fixed-support normalization
must precede any well-founded height argument.

**Scope:** the theorem gives the exact local transport and support of every consecutive
collision. It neither bounds equal-depth collisions on the canonical reset orbit nor constructs
one reset orbit with unbounded novel depth.

**Artifact:** `ReturnGuard.cancellationTangent`,
`tangentTransfer_of_consecutive_reduction`, `tangentTransfer_det`,
`cancellationTangent_isCoprime_of_base`, `tangent_reductionFactor_dvd_support`,
`tangent_novelDivisor_dvd_cyclotomic`, and
`tangentTransfer_mod_eq_zero_iff_terminal` in
[`ReturnGuardTangent.lean`](MatrixMortality/ReturnGuardTangent.lean);
`ReturnGuard.Examples.cycle_tangent_step_zero`, `cycle_tangent_step_one`, and
`cycle_tangent_step_two` in
[`ReturnGuardTangentExamples.lean`](MatrixMortality/ReturnGuardTangentExamples.lean).

**Use:** treat repeated primitive collisions as a normalized matrix cocycle rather than an
exceptional branch. Any decidability proof must first quotient fixed `S`-unit normalization and
then control the novel cyclotomic factors of this cocycle. Any universality proof must steer
successive tangent vectors through its moving kernel lines.

**Next:** construct the fixed-support-normalized tangent recurrence and decide whether its novel
normalization factors are orbitwise bounded or can encode an unbounded stack.
That is the exact fork between an orbit-specific finite nucleus and a cyclotomic stack.

### R32-S18: Fixed-support localization obstruction

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** active

The canonical multiplicative way to erase fixed parameter factors is localization. Let `S` be
the localization of a commutative ring away from `D·L·p`. Then `D`, `L`, and every chart power
`P=p^(sa)` are units in `S`. The tangent determinant identity becomes

```text
det M(P,b)  ~  1−pᵇ,
```

where `~` denotes association. Consequently

```text
M(P,b) is invertible in S  ↔  1−pᵇ is a unit in S.
```

This is the exact fixed-versus-novel separation sought after
[`R32-S17`](#r32-s17-normalized-tangent-cocycle). It also disproves the hoped-for *uniform*
finite core. For the single guarded recurrence

```text
(p,s,A,D,L)=(5,2,29,1,1),
```

[`R32-S16`](#r32-s16-cancellation-blow-up-and-unbounded-depth) supplies primitive inputs with
every positive `3`-adic cancellation depth. Localizing away from the fixed support `5` does not
erase that axis:

```text
3^i  and  3^j
```

remain nonassociated whenever `i≠j`. The proof specializes the localization to
`ℤ/(3^(min(i,j)+1))`; five stays invertible, while exactly one of the two powers vanishes.
Thus the localized recurrence retains an infinite strict divisor tower, not merely one
exceptional nonunit.

**Scope:** this excludes a finite-state theorem uniform over all primitive inputs, even after
the mathematically correct fixed-support normalization. It does not show that the one canonical
reset orbit of a guarded mortality instance visits unbounded novel depth. An orbit-specific
height bound remains viable.

**Artifact:** `ReturnGuard.tangentTransfer_localized_isUnit_iff`,
`awayFive_three_pow_not_associated_of_lt`, and
`exists_localized_nonunit_three_cancellationDepth` in
[`ReturnGuardLocalization.lean`](MatrixMortality/ReturnGuardLocalization.lean).

**Use:** do not search for a uniform finite nucleus in the localized state space. A decision
argument must exploit arithmetic restrictions of the reset orbit; a universality argument must
make that same orbit traverse an unbounded chain of novel localized divisors.

**Next:** derive an orbitwise product formula or height inequality comparing newly swallowed
cyclotomic factors with the primitive tangent height, and test it on terminal-reaching reset
executions.

### R32-S19: Canonical cyclotomic collision ladders

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

For any finite projective transfer chain

```text
Mᵢvᵢ=cᵢvᵢ₊₁,
```

the chronological product satisfies

```text
Mₖ₋₁⋯M₀v₀=(∏ᵢcᵢ)vₖ.
```

If `vₖ` is primitive, `|∏ᵢcᵢ|` is exactly the coordinate gcd of the composed
image. This is a content identity, not a descent: transfer height can grow by the amount needed
to carry every removed scalar.

The canonical residual source `(1,1)` also admits prescribed novel cancellation. If

```text
pᵃ−1=q r
```

and

```text
D=pᵃ+q p^(sa)−A,
```

then its first primitive integral step is

```text
(1,1)  ⟶  q·(1,p^(sa)+r).
```

At `A=2`, `q` is coprime to the fixed support `D·p`. Thus any chosen divisor of one
cyclotomic factor can be swallowed by a canonical reset without becoming fixed support.

The fixed guard

```text
(p,s,α,ρ)=(3,2,−64,52569)
```

has a canonical legal wait prefix `4,2,2,1`. Its primitive reductions remove

```text
8,2,292,2.
```

After deleting fixed support, the successive novel factors are `8,2,4,2`.

**Scope:** the construction prescribes one collision uniformly across the parameter family and
checks four consecutive collisions on one fixed reset orbit. It does not construct arbitrarily
long prefixes or one orbit with unbounded novel depth.

**Artifact:** `ReturnGuard.ScaledTrajectory.chronologicalProduct_mulVec`,
`ReturnGuard.ScaledTrajectory.image_gcd`,
`ReturnGuard.prescribedReset_primitiveIntegralStep`, and
`ReturnGuard.prescribedReset_factor_isCoprime_fixedSupport` in
[`ReturnGuardTangentBudget.lean`](MatrixMortality/ReturnGuardTangentBudget.lean);
`ReturnGuard.Examples.cyclotomicLadder_decodedSteps`,
`cyclotomicLadder_primitiveSteps`, and `cyclotomicLadder_novelFactors` in
[`ReturnGuardTangentExamples.lean`](MatrixMortality/ReturnGuardTangentExamples.lean).

**Use:** abandon parameter-uniform endpoint-content budgets and any claim that canonical novel
collisions are isolated. The remaining fork is per-instance boundedness versus arithmetic
synthesis of arbitrarily long collision prefixes.

**Next:** express prefix preservation as a finite `p`-adic congruence and the next moving-kernel
collision as a coprime cyclotomic congruence. Prove a CRT/Hensel extension lemma or expose the
first compatibility invariant that prevents it.

### R32-S26: Evaluation-frame gauge closure

**Kind:** structure theorem and closure
**Evidence:** formalized
**Disposition:** graduated

For a normalized mass/reset jet `j` and payload `H`, put

```text
F(j,H) = [j₀  1]
         [j₁  H],

κ(j,H) = det F(j,H) = Hj₀−j₁.
```

If the integrating factor changes to `q′` and

```text
j′ = j + (1,H)/q′,
```

then the formerly independent Cramer-frame transition is exactly

```text
T(q′,H,H′,j) = F(j,H)⁻¹ F(j′,H′).
```

Its products telescope. The moving matrix cocycle is therefore a coordinate coboundary, not
an additional dynamical state. The determinant `κ` is only the denominator for recovering two
fixed parameter coordinates from their evaluation values.

Fix an anchor `α` and write `A(j)=j₁+αj₀`. The same determinant has the intrinsic form

```text
κ(j,H) = j₀(H+α)−A(j).
```

If `j₀` is a p-adic unit and `A(j)` has anchor depth `d`, then

```text
vₚ(κ)>d  ⟹  vₚ(H+α)=d.
```

At a unit terminal payload and a positive-depth anchor, `κ` is a unit. Thus arbitrarily deep
Cramer denominators occur only on the reset-return shell; they are not an independent carry
reservoir.

**Scope:** the frame identities are exact over `ℚ`; the shell theorems require the displayed
nonzero and p-adic unit hypotheses. They do not bound the number or geometry of reset returns.

**Artifact:** `ReturnGuard.evaluationFrameTransition_eq_coboundary`,
`evaluationFrameTransition_det`, `deep_frameDefect_forces_stateDepth_eq_anchorDepth`, and
`terminal_frameDefect_isUnit` in
[`ReturnGuardFrame.lean`](MatrixMortality/ReturnGuardFrame.lean).

**Use:** reason in fixed residual coordinates. Do not retain Cramer-frame digits, parameter
jets, or denominator expansions as independent state.

### R32-S27: Rational-gap macro pumping

**Kind:** structure theorem and obstruction
**Evidence:** formalized
**Disposition:** active

Two rational residuals following the same legal wait `a` satisfy the exact similarity law

```text
vₚ(Sₐ(x)−Sₐ(y)) = vₚ(x−y)−sa.
```

For a wait word `w`, the loss is `s·sum(w)`. A perturbation deeper than that weight follows the
same branch word. Hence a return of depth `N` to one rational checkpoint pumps every bounded
number of repetitions of the same macro, losing exactly `s·sum(w)` depth per repetition.

Archimedean height prevents this from continuing indefinitely without equality. For distinct
p-adic unit rationals `x,y`,

```text
p^vₚ(x−y) ≤ 2 H(x)H(y),
```

where `H` is primitive projective height. One decoded step multiplies height by at most

```text
C = |A|+|D|+|L|.
```

Consequently, if a fixed wait macro `w` can be repeated `r>0` times from checkpoint `1`, then
either its first return is already exact or

```text
p^((r−1)s·sum(w)) ≤ 2 C^length(w).
```

A numerical violation forces an exact cycle after the first macro.

**Scope:** the pumping law works at any rational checkpoint. The final gap bound is stated at
checkpoint `1`, under one integral presentation of the guard parameters and legality of all
repetitions. It excludes storage by increasingly deep returns of one fixed macro; it does not
bound a nonperiodic schedule or a moving checkpoint.

**Artifact:** `ReturnGuard.residualRun_sub_hasValue`,
`followsResidualSchedule_of_deep_sub`, `primePower_le_rationalPairHeight`,
`residualMacroOrbit_follows_and_separates`, `repeatedMacro_exact_or_power_le`, and
`repeatedMacro_exact_of_power_gt` in
[`ReturnGuardGap.lean`](MatrixMortality/ReturnGuardGap.lean); independent synthesis in
[`m32-reset-gap-pumping-2026-07-30.md`](audits/m32-reset-gap-pumping-2026-07-30.md).

**Use:** any proposed universal orbit must move its checkpoint, change its macro, or use a
genuinely nonperiodic wait schedule. Any decision proof may instead show that sufficiently
deep returns contain a repeated macro and invoke the gap theorem.

**Next:** derive a combinatorial recurrence theorem for the canonical wait word strong enough
to force a powered factor at return depths exceeding the explicit height bound, or construct a
rational canonical orbit whose deep returns remain power-free.

## Three-Generator Four-State Frontier

Formal promotion of this section is tracked in
[#5](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/5).

### M4-C01: Two-state pushout compiler

**Kind:** compiler
**Evidence:** formalized
**Disposition:** graduated

For each data letter `x∈{b,c}`, let the role matrices

```text
R_x = [[1,V_x^R,U_x],[0,B_x^R,0],[0,0,A_x]],
D_x = [[1,V_x^D,U_x],[0,B_x^D,0],[0,0,A_x]]
```

agree on `E={(a,0,c)ᵀ}`. Embed the rule and deletion copies by

```text
ι_R(a,b,c) = (a,b,c,0)ᵀ,
ι_D(a,b,c) = (a,0,c,b)ᵀ.
```

For an arbitrary deterministic transition function
`δ : {R,D}×{b,c} → {R,D}`, let `ε_{q,x}` be one when `δ(q,x)=R` and zero
otherwise, and define

```text
X_x =
[[1, V_x^R,                  U_x, V_x^D                 ],
 [0, ε_{R,x}B_x^R,          0,   ε_{D,x}B_x^D         ],
 [0, 0,                      A_x, 0                     ],
 [0, (1−ε_{R,x})B_x^R,      0,   (1−ε_{D,x})B_x^D     ]].
```

Then

```text
X_x ι_R(v) = ι_{δ(R,x)}(R_xv),
X_x ι_D(v) = ι_{δ(D,x)}(D_xv).
```

Reading phases from the terminal column therefore gives a total suffix decoder for every
binary word. The rank is four when the two source states have different destinations and
three when they reset to the same destination.

Every `X_x` fixes `e₁`. For a terminal phase `q*`, put `C=ι_{q*}(μ,−1,t)ᵀ`,
`L=e₁ᵀ`, and `P=CL`. The fixed-anchor fracture then proves

```text
{X_b,X_c,P} mortal
  ↔ ∃w∈{b,c}⁺ : LX_wC=0.
```

This remains valid when either data generator has rank three: if an exterior column
`X_uC` vanishes, applying `L` already produces a nonempty scalar witness.

**Scope:** the theorem compiles a supplied undecidable controlled scalar source; it does not
prove that such a binary two-state source exists. The controller is deterministic and the
role pairs must agree on the complete two-dimensional upper channel.

**Use:** this is the finished matrix half of the `M₄(3)` route. Source searches should target
binary two-state controlled correspondence, not another four-dimensional separator proof.

**Artifact:** the arbitrary finite-state routing and all-word laws
`controllerMatrix_mulVec_controllerVector` and
`controllerProduct_mulVec_controllerVector` in
[`MatrixMortality/ControllerPushout.lean`](MatrixMortality/ControllerPushout.lean), specialized
by `twoStateProduct_mulVec_phaseVector`,
`twoStateDataMatrix_rank_eq_four_of_ne`, `twoStateDataMatrix_rank_eq_three_of_eq`, and
`twoStateMortalityFamily_int_mortal_iff_nonempty_zero` in
[`MatrixMortality/TwoStatePushout.lean`](MatrixMortality/TwoStatePushout.lean). The independent
algebraic reconstruction is
[`audits/m43-two-state-pushout-2026-07-24.md`](audits/m43-two-state-pushout-2026-07-24.md).

### M4-O01: Exact toggle fusion leaves an immortal core

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

For the paired controls, let

```text
H = im G_b = im G_c = span{e₁,e₃,e₄},
E = span{e₁,e₃}.
```

If a proposed fused generator satisfies

```text
SG_b = TG_b,       SG_c = TG_c,
```

then applying this identity to the common first column already gives `Se₁=e₁`. Both data
matrices also fix `e₁`, so every word over `{G_b,G_c,S}` fixes a nonzero column and cannot be
zero. One exact contextual identity is sufficient; the original invertible-two-plane argument
is stronger than necessary.

Separately, `S^r=T` with `r>0` makes `S` invertible, so no other pure power of `S` can be
rank one or zero.

**Scope:** exact contextual toggle identities and pure power codes only. A mixed macro may
break the shared plane internally and reconstruct it at its boundary.

**Use:** reject `T+P`, `TP`, `PT`, and power-coded toggle/punctuation proposals whenever they
claim exact local toggle semantics.

**Artifact:** `exactLeftToggleFusion_fixes_anchor` and `exactLeftToggleFusion_immortal` in
[`MatrixMortality/TwoStateObstructions.lean`](MatrixMortality/TwoStateObstructions.lean).

### M4-O02: Two-private-state phase signature

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Suppose an exact phase compiler shares a two-dimensional upper plane and stores every private
lower channel in a quotient `Q` of dimension at most two. Let `q₀` be the distinguished rule
phase and `q₁,q₂` two consecutive deletion phases. If two data controls agree on `q₁,q₂`, a
cyclic control carries `q₁` to `q₂` and eventually carries `q₂` back to `q₀`, all up to nonzero
scales, then the controls also agree on `q₀`.

The proof is a sharp dimension dichotomy. If `q₁,q₂` are independent, they span `Q`, so
agreement on them is global. If they are dependent, the cyclic control preserves their line
and carries that line back to `q₀`; agreement again reaches `q₀`.

In the supplied Neary source all deletion lower words coincide, whereas the two rule lower
scales differ whenever the body is nonempty. The checked generic theorem therefore makes the
putative rule scales equal, while `nearyLowerScale_rule_ne` makes them unequal.

**Scope:** exact phasewise `4=2+2` shared-channel realizations, including phase rescaling,
projective normalization, upper-plane shears, and basis changes. Nonletterwise macros and
same-zero representations remain outside the theorem.

**Use:** closes the direct extension of paired-role compression from two phases to the full
Neary deletion clock.

**Artifact:** `twoPrivateState_ruleScale_eq` proves the generic phase theorem and
`neary_twoPrivateState_phaseCompiler_impossible` instantiates the Neary scale signature in
[`MatrixMortality/PhaseSignature.lean`](MatrixMortality/PhaseSignature.lean).

### M4-S01: Odd-phase macro cut

**Kind:** structure theorem
**Evidence:** reported
**Disposition:** active

For Neary's compiled width `β=10p`, the report observes that every semantic entry phase is odd
and every even track of the woven Table 2 word is the constant letter `b`. Pair the old roles as

```text
K_x = R_xD_b,       E_x = D_xD_b.
```

Writing `m=β/2`, every claimed macro solution expands to an old solution and is forced into

```text
((K_b+K_c)(E_b+E_c)^(m−1))⁺.
```

The upper words of `K_x` and `E_x` coincide for each `x`, while both deletion-macro lower
words are `00`. The macro family therefore retains the two-plane agreement required by
[`M4-C01`](#m4-c01-two-state-pushout-compiler).

**Scope:** the existing Lean corpus proves the deletion-stroke normal form and packages the
relevant Table 2 tracks, but it does not yet state the parity invariant or the macro
solvability equivalence. This record cannot support a theorem claim until those links are
checked.

**Use:** converts the source search from four isolated roles to a rule macro followed by
`m−1` deletion macros. It does not license the closed serialization refuted by
[`M4-O03`](#m4-o03-closed-serialization-collapse).

**Next:** prove the even-track invariant for every reachable compiled queue, define the macro
morphisms in Lean, and derive the all-solution macro normal form from
`tileHistory_of_terminal_match`.

### M4-O03: Closed serialization collapse

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Let `Γ` be finite and let each semantic token `γ` have a complete binary block `Φ(γ)`.
Assume every macro-boundary queue is a concatenation of complete blocks, processing one
complete front block returns to the boundary state, and its output is a concatenation of
complete blocks determined only by `γ`:

```text
Φ(γ₁)…Φ(γₙ)  ↦  Φ(γ₂)…Φ(γₙ) Φ(τ(γ₁)).
```

At macro boundaries this is deletion-one substitution

```text
γ₁…γₙ ↦ γ₂…γₙ τ(γ₁).
```

It empties exactly when no symbol reachable from the initial word reaches a directed cycle in
the finite dependency graph `γ→η` for `η` occurring in `τ(γ)`. A reachable cycle supplies an
infinite descendant lineage; an acyclic reachable graph gives finite substitution forests.
Halting is therefore decidable.

**Scope:** finite closed tokens with locally determined complete-token output. Finitely many
instruction, junk, initialization, and terminal types merely enlarge `Γ`. Open front or tail
residues, state-dependent gauges, cancellation, and reconstruction only at larger pulse
boundaries are not covered.

**Use:** permanently reject the proposed single-active-track serialization
`x c^(m−2)b` and every elaboration that retains closed token boundaries.

**Artifact:** the proof audit is
[`audits/m43-two-state-pushout-2026-07-24.md`](audits/m43-two-state-pushout-2026-07-24.md).
The exact initial-queue criterion is
`closedSubstitutionHalts_iff_noReachableCycle` in
[`MatrixMortality/ClosedSubstitution.lean`](MatrixMortality/ClosedSubstitution.lean).

**Next:** use the checked criterion as a guardrail for every future source serializer.

### M4-O04: Exact internal/final code defect

**Kind:** obstruction
**Evidence:** formalized
**Disposition:** graduated

Suppose a binary source morphism `h` gives one semantic macro two distinct codewords `p≠q`
but preserves its upper word exactly:

```text
h(p)=h(q).
```

Then `h` is noninjective. By the two-word defect theorem, the images of the two binary letters
commute; the submonoid they generate is therefore commutative. The macro upper words

```text
û_b = u_bu_b,       û_c = 1u_b,       u_b=10^β1
```

do not commute: `û_bû_c` begins `10`, while `û_cû_b` begins `11`.

**Scope:** exact binary word-pair compilers with a state-independent upper morphism. A
state-dependent matrix gauge, an open residue, or solvability-only preservation is outside the
argument.

**Use:** distinct exact codewords cannot make one deletion macro mean “internal” in one place
and “final” in another.

**Artifact:** `binarySpell_not_injective_commute` proves the two-word defect theorem by
prefix cancellation and Euclidean descent. `neary_exact_internal_final_code_impossible`
derives the concrete macro contradiction in
[`MatrixMortality/BinaryDefect.lean`](MatrixMortality/BinaryDefect.lean).

### M4-O05: Direct two-state first-return recoding

**Kind:** obstruction
**Evidence:** reported
**Disposition:** active

Every first-return word to one state of a deterministic binary two-state controller is either a
one-letter loop or belongs to a family `emⁿr`. Four length-two returns form a rectangle, forcing
an exact factorization identity among their role maps. A loop family forces paired roles with
equal upper words to use equal exponents and hence equal lower words.

The report applies this classification to the four Neary roles and concludes that no direct
first-return recoding exists: the two deletion lower words coincide, while the rule lower words
do not.

**Scope:** direct exact recoding of the present four roles by first returns of a deterministic
binary two-state controller. A new controlled source, open residues, and nonexact matrix gauges
remain possible.

**Use:** [`M4-C01`](#m4-c01-two-state-pushout-compiler) needs a new source theorem; the present
four tiles cannot simply be relabeled by controller returns.

**Next:** reconstruct the rectangle and loop-family cases uniformly and formalize the
free-monoid cancellation argument before upgrading this record.

### M4-M01: Mixed cube-root punctuation

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** parked

The paired toggle has rational cube roots. On its three-dimensional `+1` eigenspace choose a
rational order-three map, and act by `−1` on the `−1` eigenspace; then `S³=T`.

Let `H=im G_b=im G_c` and let `k_x` span `ker G_x`. For a mixed word

```text
W = G_z S^s G_y S^r G_x,
```

the first rank drop is exactly

```text
rank(G_yS^rG_x)=2  ↔  k_y∈S^rH.
```

Writing `Π=G_y(S^rH)`, the second is

```text
rank W=1  ↔  S^(−s)k_z∈Π.
```

The search for a rank-one punctuation word is therefore a finite family of projective
incidence equations in the cube-root conjugacy parameters, followed by row- and column-boundary
alignment.

**Scope:** no parameter satisfying all incidences and boundary alignments is known. Even such
a solution would still require an arbitrary-product converse for every other mixed fragment.

**Use:** independent matrix-level fallback if the two-state source route stalls.

**Next:** solve the incidence varieties symbolically before enumerating words; reject any
candidate without a rank-stratified all-word grammar.

## Three-Letter Source Frontier

### G3-O01: Four-role macro irreducibility

**Kind:** obstruction

**Evidence:** audited

**Disposition:** active

Let the four fixed-boundary source roles be

```text
R_c = (1,    1H(q)10),      R_b = (H(b), 110),
D_b = (H(b), 0),            D_c = (1,    0).
```

Suppose a role morphism `h : {R_c,R_b,D_b,D_c}* → C*` and two nonerasing
morphisms `X,Y : C* → {0,1}*` preserve each displayed pair exactly. Then `|C|≥4`,
even when the four macro words `h(r)` have arbitrary unequal lengths and need not form a
code.

Indeed, the one-letter upper words of `R_c,D_c` force distinct one-letter macros `x,y`
with `X(x)=X(y)=1`. The one-letter lower word of `D_b` forces a third one-letter
macro `z` with `Y(z)=0` and `X(z)=H(b)`. If `C={x,y,z}`, any macro for `R_b`
must contain `z` to produce a zero under `X`. Since `X(z)` already has the complete
required length and `X` is nonerasing, that macro is exactly `z`; its lower image is then
`0`, contradicting the required `110`.

**Scope:** exact rolewise factorization through fixed macros with both new morphisms
nonerasing. It does not cover erasure, target recoding, boundary residuals, overlapping or
context-dependent codes, preservation of solvability alone, or a different computational
source.

**Use:** reject every proposal to merge or macro-expand the present four roles unless it
explicitly invokes one of the escape mechanisms outside the scope.

**Artifact:** `MatrixMortality.ExactNearyMacroFactorization.four_le_card` in
[`MacroIrreducibility.lean`](MatrixMortality/MacroIrreducibility.lean). The structure
`ExactNearyMacroFactorization` quantifies over arbitrary macro words and does not assume an
injective role code, prefix code, or equal macro lengths.

### G3-S01: Shift-equivariant zero incidence

**Kind:** structure theorem

**Evidence:** audited

**Disposition:** active

For a language `L⊆Σ*`, define its zero-language dimension over a field `K` by

```text
zdim_K(L) =
  min {d : ∃ λ,γ,(M_a)_{a∈Σ},
             w∈L ↔ λM_wγ=0}.
```

A `d`-state same-zero representation of a series `f` is equivalent to a
shift-equivariant incidence realization of its infinite Hankel zero pattern. Put

```text
r_x = λM_x,       c_y = M_yγ.
```

Then, for every prefix `x`, suffix `y`, and letter `a`,

```text
f(xy)=0 ↔ r_x c_y=0,
r_{xa}=r_xM_a,
c_{ay}=M_ac_y.
```

Conversely, rows, columns, and common letter maps satisfying these equations recover the
same-zero representation from `λ=r_ε` and `γ=c_ε`. For `d=3`, nonzero columns are
points and nonzero rows are lines in `P²(K)`; zeros are incidences.

**Scope:** a finite zero-pattern matrix of rank three is only a necessary finite shadow.
The common shift maps and rational realizability are indispensable. Zero rows or columns
must also be interpreted globally, not discarded projectively.

**Use:** formulate the surviving paired-route attack as equivariant point-line synthesis,
not exact weighted-automaton minimization. Finite nonlinear solves should enforce both
incidence and shift equations.

**Next:** construct increasing prefix/suffix instances, quotient projective gauge, and retain
finite unsatisfiable cores as candidate zero-language dimension obstructions.

### G3-M01: Free-group discrepancy engine

**Kind:** partial mechanism

**Evidence:** reported

**Disposition:** active

Carvalho's inverse-transducer reduction carries a cyclic-tag queue in the freely reduced
discrepancy

```text
Δ(w) = w⁻¹T(w).
```

On a legal transition, cancellation deletes the queue head while the transducer output
appends the production. An `H` marker counts simulated steps, a `p` marker prevents
trivial discrepancy on false paths, and every fixed point is forced to a closed transducer
path. This supplies both implicit deletion and an arbitrary-path soundness invariant.

**Scope:** the source is a free group, not a positive free monoid. The subgroup of closed
input paths has a computed free basis whose rank depends on the transducer. No bound of
three, positive encoding, or classical fixed-boundary GPCP compiler follows from the
preprint.

**Use:** audit whether the closed-path subgroup can be generated uniformly by three
positive macros or whether its control can be moved into boundaries without admitting
spurious reduced words.

**Source:** [`carvalho-2026-free-group-pcp.md`](references/carvalho-2026-free-group-pcp.md).

**Next:** extract the transducer for the smallest universal cyclic-tag source, compute its
closed-path subgroup rank, and identify exactly which formal inverses occur in the fixed-loop
converse.

## Dimension Two

### D2-S01: Projective hard core

**Kind:** structure theorem  
**Evidence:** audited  
**Disposition:** active

Every unresolved `M₂(3)` instance has two nonsingular generators `A,B` and one nonzero rank-one
generator `R=cr`. A minimal mortal word has the form `RWR`, and

```text
RWR = c(rWc)r.
```

Thus `M₂(3)` is computably equivalent to deciding whether `rWc=0` for some
`W∈{A,B}*`, equivalently point-to-point reachability on `P¹(ℚ)` under two rational Möbius
transformations.

**Scope:** the empty interior is allowed and gives `R²=0` exactly when `rc=0`. Larger generator
families may have several endpoint pairs; the three-generator hard core has one.

**Use:** every dimension-two attack should state which projective-incidence residue it decides
or encodes.

**Next:** formalize the minimal-word case split and rational-to-integer transport when the
dimension-two campaign enters its verification phase.

### D2-S02: Monotone affine path form

**Kind:** structure theorem
**Evidence:** audited
**Disposition:** stock

Suppose the two projective generators share a rational fixed point. After
sending it to infinity and removing the elementary cases, an affine conjugacy
puts them in the form

```text
F(z)=az,      G(z)=bz+1,      a,b∈ℚ×.
```

Every operational word is uniquely

```text
F^m₀ G F^m₁ G ⋯ G F^mₙ,      mᵢ≥0.
```

With `M=Σmᵢ` and `sⱼ=Σᵢ₌ⱼⁿmᵢ`, its action is

```text
w(x)=a^M b^n x + Σⱼ₌₁ⁿ a^sⱼ b^(n−j),
M≥s₁≥⋯≥sₙ≥0.
```

Conversely the monotone chain recovers every block length. The translation
terms therefore occupy one ordered exponent path with one contribution in
each `b`-layer; they are not independent `S`-units.

**Scope:** this is a normal form, not a decision procedure. Projective
source or target points at infinity are trivial because every affine map fixes
infinity. If the second translation vanishes, the pair preserves `{0,∞}`. If
both multipliers are one, reachability is a semilinear translation problem.

**Use:** preserve the path order in every affine attack. General `S`-unit
encodings that forget it may replace the problem by a strictly harder one.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#affine-normalization-and-path-form).

### D2-D01: Projectively unimodular stratum

**Kind:** decidable stratum  
**Evidence:** audited  
**Disposition:** stock

If primitive integral representatives of both projective generators have determinant `±1`,
point-to-point reachability is decidable by the established `GL₂(ℤ)` reachability machinery.
This includes rational scalar multiples of unimodular matrices.

**Scope:** it does not extend to arbitrary nonunit determinants.

**Use:** eliminate this stratum before invoking arithmetic dynamics or valuation storage.

### D2-D02: Invariant-pair stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

If the generated projective group preserves an unordered pair of distinct algebraic points,
conjugation reduces it to multiplication and inversion in a finitely generated subgroup of a
number field of degree at most two. The report reduces rational point reachability to effective
semilinear membership in an abelian-by-`C₂` group.

**Scope:** the recognition algorithm and effective semilinearity require independent checking.
The claim does not cover a group with only one common fixed point.

**Use:** separate elementary projective groups from the non-elementary residue before invoking
height growth or valuation universality.

**Next:** audit the invariant-pair recognition cases and the positive-semigroup reachability
step.

### D2-D03: Common-multiplier stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

For finitely many rational affine maps `z ↦ az+b_i` with one nonzero rational multiplier `a`,
rational endpoints, and regular control, the report reduces reachability to semilinear path
weights when `a=±1` and to corrected finite target discounted-sum reachability otherwise.
Fixed positive powers of one rational base reduce by regular block substitution.

**Scope:** the result depends on the corrected finite-word discounted-sum theorem. Different
multipliers with independent valuation vectors remain outside it.

**Use:** remove common-slope and common-positive-base affine candidates from the dimension-two
undecidability search.

**Next:** verify the corrected source theorem, reversal and final-letter constructions, and
negative-multiplier parity handling.

### D2-D04: Single-base affine stratum

**Kind:** decidable stratum  
**Evidence:** reported  
**Disposition:** active

For

```text
G_q^± = {z ↦ εqⁿz+t : ε∈{±1}, n∈ℤ, t∈ℤ[1/q]},
```

the report claims decidability of point incidence for every rational subset represented by a
finite automaton. It reduces the incidence set to a coset of an effectively cyclic stabilizer
and invokes Boolean emptiness for rational subsets of `BS(1,q)`, followed by an index-two sign
extension.

**Scope:** this is not a theorem for several independent rational bases. Recognition of the
ambient single-base condition and the coset construction require independent checking.

**Use:** reject any universality proposal confined to one `BS(1,q)`-type affine group.

**Next:** audit the stabilizer calculation, effective word construction, and transfer through
the index-two extension.

### D2-D05: Prescribed translation count

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

For normalized maps

```text
F(z)=az,      G(z)=bz+1,
```

rational endpoints, a prescribed number `n` of occurrences of `G`, and an
optional regular control language, reachability is decidable.

For `a=p/q` with `|p|≠q`, zero evaluation of any integer digit polynomial at
`p/q` is recognized by a finite carry automaton. If

```text
P(X)=(qX−p)E(X),
```

its digits and carries obey

```text
dₖ=qeₖ₋₁−peₖ.
```

Scanning in the contracting coefficient direction bounds `|eₖ|` by the
maximum digit size divided by `||p|−|q||`. For prescribed `n`, the endpoint
equation has only `n+2` ordered coefficient markers; coincident markers add
and arbitrary gaps encode the unbounded `F`-runs. A finite marker automaton,
the carry automaton, and a DFA for reversed regular control can therefore be
intersected. The cases `a=1` and `a=−1` reduce to equality and parity.

**Scope:** `n` is supplied to the algorithm. This does not decide the
unconstrained union over every translated-letter count.

**Use:** any valuation, height, or congruence argument that restricts `n` to a
finite computable set now yields a terminating affine reachability algorithm.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#fixed-translated-letter-count).

### D2-D06: Private-prime peeling

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

For

```text
F(z)=az,      G(z)=bz+1,
```

suppose some prime `p` satisfies `v_p(a)=0` and
`β=v_p(b)<0`. In a word containing `n≥1` occurrences of `G`, the first
translation term is the unique least-valued translation term. Its valuation
differs from that of the endpoint term by the constant `v_p(x)+β`.

Outside the critical source shell `v_p(x)+β=0`, the valuation of the target
therefore determines the only possible `n`:

```text
n=(v_p(y)−v_p(x))/β        if v_p(x)+β<0,
n=1+v_p(y)/β               if v_p(x)+β>0.
```

Impossible integers are rejected; `y=0`, `x=0`, and `n=0` are handled
separately. [`D2-D05`](#d2-d05-prescribed-translation-count) decides the
remaining fixed-count instance, including regular control.

If `v_p(b)>0`, reverse the word and conjugate by `u=−bz`. The translated
multiplier becomes `b⁻¹`, and the corresponding noncritical condition is
`v_p(y)≠0`.

**Scope:** the theorem needs a prime absent from the pure multiplier `a` but
present in `b`. It leaves one exact source shell for negative valuation, or
one target shell for positive valuation.

**Use:** peel mixed-prime affine pairs before invoking module or building
machinery. It decides every prescribed endpoint outside the critical shell
without bounding the pure-letter runs.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#private-prime-peeling).

### D2-D07: Bounded valuation orthants

**Kind:** decidable stratum
**Evidence:** audited
**Disposition:** stock

Let finitely many rational affine maps `fᵢ(z)=aᵢz+bᵢ` preserve a common
bounded rational interval. Suppose that at every prime the weights

```text
−v_p(a₁), …, −v_p(a_k)
```

have one weak sign. Then rational point-to-point reachability is decidable,
including under regular control.

For nonpositive slope weights, denominator weight never exceeds the maximum
of its current value and the translation weights. For nonnegative slope
weights, once the current weight exceeds every translation weight, it cannot
decrease. A successful path therefore has an effective denominator bound at
every input prime. Rational affine operations introduce no new denominator
primes, and a bounded interval contains only finitely many rationals with a
fixed denominator bound. The problem reduces to finite graph reachability.

The hypotheses are effective: rowwise valuation signs are computable, and a
common invariant rational interval is a rational linear-feasibility problem.
For example,

```text
z↦(2/3)z,      z↦(4/5)z+1/5
```

is covered on `[0,1]` despite multiplicatively independent slopes.

**Scope:** boundedness is essential to finiteness. Incompatible valuation
signs at even one prime remain outside the theorem.

**Use:** this is the first audited mixed-prime affine stratum beyond the
common-multiplier and single-base records.

**Source:** the deterministic denominator-weight precursor is
[`bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.md`](references/bournez-kurganskyy-potapov-2018-piecewise-affine-reachability.md).
The nondeterministic regular-control theorem is proved in
[`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#bounded-valuation-orthants).

### D2-M01: Benchmark critical shell

**Kind:** partial mechanism
**Evidence:** audited
**Disposition:** active

The benchmark

```text
z↦(2/3)z+1,      z↦(3/5)z+1
```

is conjugate by `h(z)=15−5z` to

```text
F(z)=(2/3)z,      G(z)=(3/5)z+1.
```

Private-prime peeling at `p=5` decides every original source satisfying
`v₅(3−x)≠0`. A second chart and reversed peeling at `p=2` decide every target
satisfying `v₂(6y−15)≠0`. Only the endpoint shell

```text
v₅(3−x)=0,      v₂(6y−15)=0
```

survives both tests.

In normalized coordinates, write a critical state as `5u` with `v₅(u)=0`.
A block `F^mG` remains critical exactly when

```text
T_m(u)=(1+3u(2/3)^m)/5
```

is a `5`-adic unit. Its first guard digit forces odd `m` when `u≡2 mod 5`,
even `m` when `u≡3 mod 5`, and forbids continuation for residues `1,4`.
Once a path leaves the shell, it cannot return, and every fixed exit has a
decidable suffix by [`D2-D06`](#d2-d06-private-prime-peeling).

**Scope:** the guarded maps describe every maximal shell-preserving prefix.
They do not yet decide the infinite union of possible exits. This corrects the
stronger claim that the benchmark had been reduced to a self-contained shell
reachability problem.

**Use:** concentrate the benchmark attack on an effective representation of
reachable critical states together with accepting exits. The main alternatives
are a finite redundant base-`5` carry nucleus or an unbounded-counter
simulation through growing exponent congruences.

**Artifact:** [`audits/dimension-two-affine-peeling-2026-07-25.md`](audits/dimension-two-affine-peeling-2026-07-25.md#critical-shell-dynamics).

**Next:** decide whether the exponent residues required modulo `5^k` admit a
finite synchronized representation across all carry depths.

**Issue:** [#7, Formalize affine peeling and decide the `M₂(3)` benchmark
shell](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/7).
