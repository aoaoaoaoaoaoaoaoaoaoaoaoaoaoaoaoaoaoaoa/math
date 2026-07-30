# Matrix Mortality Frontier Campaign

Established-result ledger and dimension-two research audit: 2026-07-25. A question mark means
“not resolved by any valid result found in the present literature audit,” not an assertion that
no unpublished argument exists.

Reusable lemmas, obstructions, certificates, and partial mechanisms from unsuccessful attacks
are indexed in [`SALVAGE.md`](SALVAGE.md). Its evidence labels are authoritative; this file
records only their strategic consequences.

## The source theorem

The source result is no longer conditional on the Neary–Rote terminal tile:

> **Theorem.** `GPCP(4)` over a binary target alphabet is undecidable, even with empty left
> boundaries, one empty right boundary, and nonempty morphism images.

For Neary's four ordinary pairs, the fixed-boundary equation is

```text
∃w ∈ {R_c,R_b,D_c,D_b}*: U(w)10^β = V(w).
```

A zero-run automaton forces every matching word into exact deletion-width blocks, and a
queue-history theorem proves that those blocks constitute a lawful restricted tag computation.
Conversely, every halting computation emits such a match. This equivalence is formalized in
`MatrixMortality/NearyEncoding.lean`. The fixed universal machine, Cocke–Minsky compiler,
one-hot cyclic compiler, Table 2 implementation, arbitrary-execution converse, primitive-recursive
target constructors, many-one reductions, and no-decider theorems are formalized through
`MatrixMortality/Undecidability/UniversalNeary.lean`. Neary's Lemma 9 is historical provenance,
not a proof premise.

Adding a fresh delimiter pair `(10^β#, #)` and fixed-length binary recoding also gives a
corrected five-pair PCP family with primitive terminality. Rote's long unary guard is no longer
used.

Nicolas (2008) and CHHN (2014) explicitly list `GPCP(4)` as open. Exact-phrase searches,
forward-citation inspection of Neary's paper, and inspection of Rote's 2024/2025 versions found
no later statement of this consequence. Rote notices the special terminal role but does not
state the bounded-GPCP improvement. This is a strong novelty indication, not an absolute
bibliographic certificate; author confirmation is mandatory before priority language is used.

## Cross-problem consequences

The source representation, paired-role quotient, and shared-channel binary compiler establish
the Pareto-minimal scalar points

```text
Z₃(4), Z₄(3), Z₆(2).
```

CHHN's scalar-to-corner reduction gives

```text
R₃(5), R₄(4), R₅(3), R₇(2).
```

The structured forms `Z̊₃(4)`, `Z̊₄(3)`, and `Z̊₆(2)` have common first column `e₁`. The
six-state binary compiler supersedes the earlier `Z₇(2)` packing consequence; its corner lift
similarly supersedes `R₈(2)`.

## The reusable compiler

The rank-one construction is best viewed as a fixed-boundary compiler. Let `ρ` be a matrix
representation whose letter matrices are nonsingular, and consider

```text
ℓᵀ P ρ(w) S c = 0,
```

where `P,S` encode fixed left and right words. Put

```text
a = (S c)(ℓᵀ P).
```

Then

```text
a ρ(w) a = (S c) [ℓᵀ P ρ(w) S c] (ℓᵀ P).
```

In an arbitrary product, nonsingularity of the `ρ`-blocks makes the two exterior vectors
nonzero; the product vanishes exactly when one internal bridge scalar vanishes. Both fixed
boundaries therefore cost one repeated rank-one generator, not two boundary generators.

This subsumes terminal-tile absorption and the older Claus endpoint construction. Its counting
law is the important limitation:

```text
m active interior tile roles  +  one rank-one separator
                         =  m+1 mortality generators.
```

Boundary-only tiles are free; an interior-active tile is not. Neary's tile 5 is boundary-only,
but tiles 1–4 all remain active. Tile 1 is forced first yet also recurs during the simulation, so
absorbing the initial occurrence does not reduce the active alphabet. Consequently this compiler
is exhausted at `M₃(5)`. Reaching `M₃(4)` by the same route requires a source with at most three
interior roles, equivalently an undecidable `GPCP(3)` family.

## The paired-role compiler

In the side-normal word-pair representation, Neary's rule and erasure matrix for a fixed tag
letter agree on the two-dimensional upper-word plane. On two three-dimensional phase spaces,
the anti-diagonal copy of this plane can therefore be quotiented out. Two data generators and
one suffix-phase toggle act on the resulting four-dimensional space. Every control word decodes
to a four-role word, and every four-role word has an encoding.

This gives structured `Z̊₄(3)`. Adding the established outer-product separator gives `M₄(4)`;
the arbitrary-product converse uses the controls' common fixed column instead of nonsingularity.
The machine-checked implementation is in `PairedCompression.lean` and `PairedMortality.lean`.
A public-literature search through 2026-07-22 found no earlier `Z₄(3)`, `M₄(4)`, paired-role
decoder, or common-column mortality converse. The quotient itself and the rank-one separator
are prior art; see `audits/m44-prior-art-2026-07-22.md`.

## The binary compilers

The four-role alphabet factors as a rule/deletion bit and a tag-letter bit. A two-bit decoder
therefore needs one complete three-coordinate state and one partial state. Rule and deletion
share the partial upper channel, reducing the generic partial state to three coordinates. The
resulting two `6×6` integer matrices preserve the source coefficient on every binary word; an
odd final bit preserves the coefficient, and reversed block encoding is surjective. Transpose
and word reversal give structured `Z̊₆(2)`.

A second binary compiler exploits the stroke schedule rather than role factorization. At fixed
deletion width `β`, position modulo `β` determines whether the selected tag letter acts as a
deletion or a rule. Two `(β+2)×(β+2)` integer matrices then preserve the source coefficient on
every binary word. Reversed stroke encoding is surjective, and a zero coefficient forces a
complete tile history; incomplete clock cycles cannot create witnesses. At `β=3`, the native
series has exact rational rank five for every nonempty body. These claims are formalized in
`ScheduledBinary.lean` and `ScheduledBinaryRank.lean`; see
[`MM-C03`](SALVAGE.md#mm-c03-scheduled-binary-compiler) and
[`MM-O05`](SALVAGE.md#mm-o05-width-three-scheduled-rank).

This does not add a frontier point. Neary's universality compiler sets `β=10p`, with `p` the
cyclic-tag program period. The fixed-width audit found no universality theorem for the required
binary deletion-width-three family. At width three the construction would imply `Z₅(2)`,
`M₅(3)`, and `R₆(2)`; at the presently established variable width it gives no fixed matrix
dimension. See `audits/scheduled-binary-fixed-width-2026-07-24.md`.

Full mortality requires coding the four payloads and the rank-one separator. The complete
prefix code

```text
0, 100, 101, 110, 111
```

has four prefix states and gives a `12`-state deterministic matrix transducer. The word `00`
synchronizes all start states. Paired-role agreement supplies two common left annihilators, so
both binary generators have image in one integral `10`-dimensional subspace. Restriction to that
image is exact. If a restricted product is zero, appending `0` gives a zero `12`-state product;
restriction therefore introduces no false mortality witness. This proves `M₁₀(2)`, and zero
padding gives `M_d(2)` for every `d≥10`.

Both compilers and their arbitrary-word converses are machine-checked in `PairedBinary.lean`,
`WeightedTransducer.lean`, and `PrefixMortality.lean`. A public-literature search through
2026-07-24 found no earlier `Z₆(2)`, `R₇(2)`, or `M₁₀(2)`. Binary coding and generic alphabet
reduction are prior art; the priority claims concern the shared-channel and common-image
constructions.

## Current mortality staircase

After terminal absorption, paired-role compression, binary compilation, dimension padding, and
CHHN's generator–dimension trade, the established Pareto-minimal undecidable points are

```text
M₃(5), M₄(4), M₆(3), M₁₀(2).
```

The unknown cells immediately below this staircase are:

| Cell | What would suffice | Automatic reward |
| --- | --- | --- |
| `M₃(4)` | three-active-role fixed-boundary PCP / `GPCP(3)`, or a new same-dimension generator compiler | by CHHN, also `M₉(2)` |
| `M₄(3)` | an undecidable binary two-state controlled scalar source, or an open-residue matrix macro | by CHHN, also `M₈(2)` |
| `M₅(3)` | a five-state binary same-zero root, a toggle/separator fusion, or fixed-width-three scheduled universality | supersedes `M₆(3)`; `M₁₀(2)` is already known |
| `M₉(2)` | a changed physical pair, changed-zero-series compiler, or nonlinear reduction; the present pair spans `M₁₀(ℚ)` | improves the two-generator threshold by one |
| `M₂(k≥3)` | a qualitatively different decidability or undecidability argument | settles the dimension-two wall |

The scalar result `Z₆(2)` gives `M₆(3)` after adjoining a separator; that mortality point was
already obtained from `M₃(5)` by CHHN packing.

## The hard stratum

The completed improvements all preserve enough exact structure to admit a finite decoder:
boundary absorption, common-channel quotients, fixed-width clocks, prefix transducers, and
common-image restriction. Their arbitrary-word converses assign every free-monoid word a
controlled interpretation. The remaining cells begin where that program pays an unavoidable
state or generator tax.

Three obstructions recur.

1. **Exact behavior costs dimension.** Hankel certificates block further exact minimization;
   shared-channel phase compilers admit only low-period scale signatures; literal prefix
   parsers retain too many live source coordinates.
2. **Closed syntax loses universality.** A finite self-contained token whose output is a word
   of complete tokens induces decidable deletion-one substitution. Constraining witnesses to a
   regular code language is unavailable because mortality quantifies over every word.
3. **The target predicate is weaker than the available representation.** Mortality needs only
   one zero product, scalar reachability only one zero coefficient, and projective incidence
   only one orbit hit. Exact coefficient preservation carries information the target never
   asks for, but discarding it makes malformed-word soundness the central theorem.

The internal-word sandwich compiler [`MM-C04`](SALVAGE.md#mm-c04-internal-word-sandwich-minimization)
qualifies this diagnosis. Exact invariant subquotients do not need a fresh malformed-word
proof when a physical low-rank repair word already exists: wrapping any quotient zero by that
word lifts it upstairs. Their obstruction is instead algebraic saturation. For the present
ten-state pair, [`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair) proves that the word
span is already the full matrix algebra.

Outside that exact-repair lane, the common problem remains **unbounded synchronization under
adversarial word choice with no explicit control-state budget**. A successful construction must
store semantic phase outside an ordinary finite closed parser: in an open suffix or tail
residue, free cancellation, a numerical carry, projective incidence, a semigroup ideal, or an
arithmetic normal form. The decidability side of `M₂(3)` asks for the dual result: prove that
this hidden state nevertheless admits an effective finite or semilinear description.

This changes the value of the frontier. The remaining cells are no longer principally missed
packings. They ask whether zero-set semantics, nonlocal residues, or arithmetic structure can
replace exact finite-state simulation.

## Ranked attacks

### 1. Two-state control and open residues: `M₄(3)`

The matrix half is complete. The pushout compiler
[`M4-C01`](SALVAGE.md#m4-c01-two-state-pushout-compiler) represents any deterministic
two-state role controller over `{b,c}` by two `4 × 4` integer data matrices. A rank-one third
matrix gives mortality exactly when the controlled binary scalar series has a nonempty zero.
The decoder is total on all binary words, and reset transitions may make a data matrix singular
without weakening the mortality converse.

The source theorem is missing. Fazekas and Seki define the required one-tag-with-states model
and cite unrestricted circular-automata universality, but neither their paper nor the audited
literature supplies the exact two-state binary bound
([local synopsis](references/fazekas-seki-2023-freezing-one-tag-states.md)).

The present Neary source cannot be inserted letterwise:

- exact local toggle fusion preserves an immortal two-plane
  ([`M4-O01`](SALVAGE.md#m4-o01-exact-toggle-fusion-leaves-an-immortal-core));
- agreement at two consecutive deletion phases in a two-private-state quotient propagates
  around the cycle to the rule phase, contradicting the unequal Neary rule scales
  ([`M4-O02`](SALVAGE.md#m4-o02-two-private-state-phase-signature));
- the direct binary two-state first-return recoding is reported impossible
  ([`M4-O05`](SALVAGE.md#m4-o05-direct-two-state-first-return-recoding)).

The odd-phase macro cut [`M4-S01`](SALVAGE.md#m4-s01-odd-phase-macro-cut) remains useful but
does not restore the discarded route. Pairing every semantic role with the following `D_b`
produces rule macros `K_x` and deletion macros `E_x`, reportedly with every solution forced
into `(KE^(m−1))⁺`. Serializing those macros as complete blocks is impossible:
[`M4-O03`](SALVAGE.md#m4-o03-closed-serialization-collapse) proves that every finite
closed-token implementation collapses to decidable deletion-one substitution. Distinct exact
internal and final block codes also fail by
[`M4-O04`](SALVAGE.md#m4-o04-exact-internal-final-code-defect).

Two architectures survive.

1. **Open-tail source.** Build four appendants whose invariant retains a phase-bearing proper
   suffix at the front and an incomplete tail at the rear. Emission must merge with that tail;
   it cannot be a concatenation of complete semantic objects. The next state and residue must
   be reconstructed only at a larger pulse boundary.
2. **State-gauged matrix macro.** Let incomplete matrix fragments break the shared upper plane
   and reconstruct it only at macro boundaries, preserving the zero set rather than every
   coefficient. The cube-root incidence mechanism
   [`M4-M01`](SALVAGE.md#m4-m01-mixed-cube-root-punctuation) is the concrete fallback, but it
   still lacks a boundary-aligned rank-one word and an all-fragment converse.

The next source experiment should specify an open-residue invariant before choosing appendants.
The next matrix experiment should solve the cube-root incidence varieties symbolically before
enumerating words. Any proposal whose semantic queue is a finite word of complete tokens is
already closed.

### 2. Zero-set compression and fused punctuation: `M₅(3)`

The literal CHHN packing has no common invariant line or hyperplane. The all-placement
certificate [`MM-O01`](SALVAGE.md#mm-o01-all-placement-packing-rank) now formally proves that
its selected coefficient series has exact representation dimension six for every placement.
This closes exact minimization of that packing in five states.

The paired four-state scalar system closes a second exact route. Lean certifies a uniform
nonsingular four-by-four Hankel section
([`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series)), while the two-channel boundary
exact diagonal bridge. Their composed theorem
`paired_exact_diagonal_twoChannel_state_lower_bound` therefore requires at least six states.
Both conclusions concern exact series; neither constrains another series with the same zero set.

The internal-word sandwich compiler
[`MM-C04`](SALVAGE.md#mm-c04-internal-word-sandwich-minimization) initially offered a way
around every parser obligation. It is now closed on the canonical paired-binary mortality
family: [`MM-O11`](SALVAGE.md#mm-o11-full-algebra-paired-binary-family) proves that its word
span is `M₆(ℚ)`, so every nonzero sandwich has exact dimension six. All 120 literal CHHN
packings are likewise full-algebra at the benchmark, although that finite modular sweep is not
a uniform theorem. The sandwich compiler becomes live again only with a different physical
six-state family.

Three live routes remain.

1. Construct a five-state binary series with nonsingular letter matrices, the source zero set
   on complete two-bit blocks, and nonzero values on odd words; then adjoin the ordinary
   rank-one separator. The unused identity `(V_b^D,B_b^D)=(V_c^D,B_c^D)` suggests processing
   the common deletion channel before the symbol bit is known. A four-state root would prove
   the stronger `M₄(3)` result.
2. Fuse the paired toggle and separator inside one five-dimensional generator. The
   off-diagonal companion interface
   [`MM-M01`](SALVAGE.md#mm-m01-off-diagonal-companion-interface) supplies a complete bridge
   grammar once a physical control word realizes it. Pure delimiter powers cannot supply
   punctuation while preserving the exact isolated toggle
   ([`MM-O06`](SALVAGE.md#mm-o06-pure-power-punctuation-obstruction)). The new setter candidate
   [`MM-M03`](SALVAGE.md#mm-m03-five-state-setter-punctuation) instead uses the mixed word
   `S²A_cS³=λC̃L̃`. It proves the regular decoder and halting-to-mortality implication.
   Its entire malformed-word converse is the projective avoidance problem
   [`MM-S01`](SALVAGE.md#mm-s01-square-run-projective-normal-form): rational Möbius maps
   `Φ_z` must avoid their poles from the reset values `0` and `1/μ`, except for a genuine
   terminal match. The source boundary fixes `r=t/μ`
   ([`MM-O07`](SALVAGE.md#mm-o07-setter-parameter-rigidity)); generic parameter selection is
   not a live escape. Reversing the two nonzero ternary digits is lawful and strictly sharper:
   [`MM-M04`](SALVAGE.md#mm-m04-swapped-digit-setter) preserves the regular decoder and mixed
   separator while moving the common projective center below zero and making every transfer
   orientation preserving.
3. Use the scheduled compiler [`MM-C03`](SALVAGE.md#mm-c03-scheduled-binary-compiler).
   A fixed binary deletion-width-three universality theorem would finish the reduction
   immediately. None was located. The constructive alternative is to replace the variable
   phase clock by a constant-state delimiter or punctuation mechanism and prove that every
   malformed placement is excluded by the terminal-match normal form. The width-three
   rank-five theorem [`MM-O05`](SALVAGE.md#mm-o05-width-three-scheduled-rank) shows that five
   exact states are necessary at that width; it does not obstruct a same-zero clock
   compression or delimiter fusion.

The swapped setter is now the sharpest constructive route. Its next experiment is not another
five-dimensional word search: enumerate side products by `(U,V,A,B)`, propagate the
one-dimensional projective state exactly, and seek a finite invariant separating every
nonterminal orbit from every pole. Congruence quotients, `3`-adic valuation with pulse phase,
signed interval partitions, and self-synchronizing suffix states are the first candidates.
A first peeling theorem
[`MM-S02`](SALVAGE.md#mm-s02-reset-zero-projective-peeling) now excludes every false pole
after one transfer from the ordinary reset. It also shows why valuation alone is insufficient:
all poles occupy two `3`-adic shells, while bounded malformed orbits rapidly saturate their
finite residue classes. The next abstraction must retain mismatch depth together with pulse or
suffix history. The centered carry theorem
[`MM-S03`](SALVAGE.md#mm-s03-centered-setter-carry) supplies that interface:

```text
X'=3^mY,      Y'=(RP−HV)Y+RHμVX.
```

Away from equal valuations, the valuation gap updates by
`d'=m−min(d,s)` with `s∈{1,β}`. It reduces the first possible two-transfer
collision to three rigid all-`c`/single-`D_b` block families. From the
distinguished boundary, the resonant carry is exactly the longest common
suffix of the upper terminal spelling and the lower spelling.
[`MM-S04`](SALVAGE.md#mm-s04-reverse-suffix-discrepancy) gives its exact
right-to-left machine. It is a word-valued PCP discrepancy queue, not a finite
pulse state. At either dangerous gap, however, the unprocessed left fringe has
upper length at most `β+2` or `2β+1`. The next proof must therefore quotient
the internal discrepancy queue semantically while preserving these bounded
targets; a larger residue modulus or phase-only automaton cannot suffice. The
first target is now gone:
[`MM-S05`](SALVAGE.md#mm-s05-distinguished-boundary-beta-shell) proves that
the `d=β` branch at boundary `1` cannot reach either single-erasure pole. Only
the valuation-one target survives there. Its distinguished normalized value
`Δ=H` is exactly a genuine terminal match. The divisor normal form
[`MM-S06`](SALVAGE.md#mm-s06-valuation-one-divisor-normal-form) writes every
other integral target on one of finitely many rays indexed by
`q∣(ρ+1)` and `a₀∣Hμ`; only one positive parameter remains unbounded. The
digit swap removes that unbounded parameter:
[`MM-S07`](SALVAGE.md#mm-s07-swapped-digit-finite-slope-reduction) makes the
centered coefficient strictly negative and forces every integral
valuation-one pole into a finite set of primitive slopes. The common scale of
the two code integers remains unbounded, so this is not yet a finite word
search. [`MM-S08`](SALVAGE.md#mm-s08-swapped-distinguished-boundary-beta-shell)
excludes the residual value `2μ`, so the complete distinguished-boundary
`β` shell is safe.
[`MM-S09`](SALVAGE.md#mm-s09-canonical-swapped-residue-cannot-hit-a-pole)
also excludes the unavoidable all-`D_c` valuation-one residue at every
compiler-emitted width.
[`MM-S10`](SALVAGE.md#mm-s10-swapped-target-suffix-sieve) fixes the last
`β+2` digits of every pole-compatible lower word and excludes the recurrent
nonhalting residue `Δ=ρ−1`. The immediate question is which other positive
valuation-one discrepancies survive this suffix sieve without already
certifying source halting. Exact bidirectional diagnostics at `β=3`, body `bbcc`, exclude every
false-pole word of at most six projective blocks when each regular block has
role length at most three; this is computational evidence only.
A single explicit nonterminal pole orbit kills this family; a closed invariant proves
`M₅(3)`. The same-zero binary root and fixed-width-three source remain independent fallbacks.

### 3. Two-generator realization: `M₉(2)`

The exact obstruction is now complete. The physical word `000` in the restricted ten-state
pair is rank one, but its scalar sandwich has exact Hankel rank ten. More strongly, the word
products of the pair span `M₁₀(ℚ)`
([`MM-O08`](SALVAGE.md#mm-o08-full-algebra-prefix-pair)). The pair therefore has no nonzero
proper invariant subspace or quotient, and every nonzero internal-word sandwich has exact
realization dimension ten. Common-image restriction, kernel quotient, reachable/observable
minimization, and internal punctuation cannot reach nine states from this pair.

The surviving route must change the physical pair, change its nonzero values while preserving
zeros, or use a nonlinear compiler. A literal binary prefix tree for five source symbols has
four internal states, while a literal two-state ternary tree cannot obtain a five-state
common-image restriction ([`MM-O09`](SALVAGE.md#mm-o09-two-state-ternary-prefix-image)).
Neither statement excludes a state-dependent gauge or same-zero transducer.

### 4. Three-letter correspondence and direct mortality: `M₃(4)`

The public-literature audit through 2026-07-24 found no resolution of `GPCP(3)` or
`M₃(4)`. The two targets should not be conflated.

```text
GPCP(3) undecidable
        ⇒ Z₃(3)
        ⇒ M₃(4).
```

The converse is absent. A direct mortality proof may change every nonzero coefficient, use
singular ideals or projective incidence, or abandon word-pair morphisms altogether. Classical
GPCP must still express equality of two free-monoid morphisms with fixed boundaries. This
strict containment of proof obligations is the sound reason to rank a direct `M₃(4)` attack
above a genuine `GPCP(3)` theorem. The numerical probabilities in the exploratory
pre-mortem are not evidence and are not retained.

The foundational reward points the other way. `GPCP(3)` would immediately yield

```text
Z₃(3), M₃(4), R₃(4), R₄(3), Z₅(2), R₆(2), M₉(2),
```

through the standard scalar, corner, mortality, and packing reductions. A direct mortality
construction certifies only `M₃(4)` and its mortality packing consequences unless it carries
an additional scalar interpretation.

#### Closed exact routes

The present four roles are

```text
R_c = initialization / c-rule,       R_b = b-rule,
D_b = deletion of b,                 D_c = deletion of c.
```

Two broad compressions are now excluded.

The exact nonerasing macro obstruction
[`G3-O01`](SALVAGE.md#g3-o01-four-role-macro-irreducibility) proves that no
fixed rolewise macros over three source letters reproduce these four word pairs exactly.
Unequal macro lengths, noninjective role codes, and failure of prefix-freeness do not help.
A surviving compiler must use erasure, target recoding, boundary or context residuals,
overlap, solvability-only preservation, or a different source. Lean checks the obstruction as
`ExactNearyMacroFactorization.four_le_card`.

The body-independent Hankel certificate
[`MM-O04`](SALVAGE.md#mm-o04-uniform-rank-four-paired-series) proves that the
current three-control paired coefficient series has exact rank four already on `{b,t}*`.
Similarity, exact quotient or restriction, and nonzero per-letter rescaling cannot produce a
three-state realization. A surviving matrix route must change the nonzero values and preserve
only the zero language, or replace the compiler.

The fixed-first property also remains useless: `R_c` recurs whenever the `c` rule fires.
Absorbing its initial occurrence does not remove its interior role.

#### Structural lower boundary

The decidable two-letter endpoint is not merely a failed search for universality. Binary
equality sets of non-periodic morphisms are generated by at most two words, with strong
first- and last-letter separation in rank two
([Holub](references/holub-2012-binary-equality-sets.md)). Binary GPCP admits the
beginning-block, end-block, successor, and reduction-tree analysis developed by Halava and
Holub. Marked GPCP is decidable
([Halava–Harju–Hirvensalo](references/halava-harju-hirvensalo-1999-marked-gpcp.md)).

These theorems delimit a ternary construction. It must generate residual ambiguity absent
from the binary successor tree, and it cannot become marked after recoding. Hadravová's
historical account also records regularity of ordinary ternary equality sets as open; that
homogeneous question is not itself fixed-boundary `GPCP(3)`, but it confirms that the jump
from two source letters has resisted the standard equality-set theory.

The conventional few-rule route pays a fixed tax. Nicolas proves

```text
ACCESSIBILITY(k) undecidable ⇒ GPCP(k+2) undecidable.
```

Matiyasevich and Sénizergues supply undecidable three-rule accessibility, hence `GPCP(5)`.
Through this compiler, `GPCP(3)` would require an undecidable one-rule accessibility source.
A useful rewriting attack must therefore either find a tighter compiler or build a
computational source whose certificate has three morphism schemas natively. A machine with
three symbol types but many transition rules does not meet this count.

#### Research lanes

| Lane | Available leverage | Decisive obstruction or obligation |
| --- | --- | --- |
| Shift-equivariant zero incidence | Same-zero dimension three is point-line incidence in `P²`, formalized by [`G3-S01`](SALVAGE.md#g3-s01-shift-equivariant-zero-incidence) | Finite minimum rank is insufficient; all prefixes and suffixes must share three common shift maps over `ℚ` |
| Inverse-transducer discrepancy | Free cancellation performs queue-head deletion and Carvalho proves an all-path fixed-loop converse; see [`G3-M01`](SALVAGE.md#g3-m01-free-group-discrepancy-engine) | The closed-path subgroup has instance-dependent rank; inverses, free reduction, and subgroup control must be compiled into three positive letters |
| Context and sliding-block codes | Adjacent ternary symbols can carry four semantic roles without fixed role macros | GPCP quantifies over the full free monoid; every boundary fragment, phase shift, and invalid overlap must be algebraically harmless |
| Erasure and target recoding | Erasure escapes `G3-O01`; longer target atoms can split the one-letter images used in its proof | Empty contributions and code fragments create new boundary matches unless a global normal form excludes them |
| New three-schema rewriting source | Bi-tag, cyclic-tag, Lag, queue, and small semi-Thue systems separate data motion from finite control | Count transition schemas, not data symbols; the program table must live in boundaries or target words without adding source letters |
| Exclusive stochastic or affine recognition | Zero/nonzero languages can be much smaller than exact coefficient series | Affine normalization, quantum measurement, and finite pair separation are not raw integer scalar-zero representations |
| Direct projective or affine dynamics | Three `3 × 3` controls can encode switched dynamics on two homogeneous coordinates | Unguarded matrix choice demands an irreversible checksum for every illegal branch |
| Semigroup ideals and reset structure | Rees or Brandt incidence can make incompatible phases fall into a zero ideal | Natural representations usually spend dimension on control states; the full arbitrary-product grammar remains mandatory |

The first, sixth, seventh, and eighth lanes principally target direct `M₃(4)`. The third,
fourth, and fifth can produce a genuine `GPCP(3)` theorem. The free-group lane is hybrid:
it supplies the missing deletion semantics but not yet the bounded positive source.

#### Operational program

The highest-yield direct experiment is not another exact minimization. For increasing finite
prefix and suffix sets, solve over `ℚ` for

```text
r_x, c_y ∈ ℚ³,       T_a ∈ ℚ^(3×3),
r_x c_y = 0  ↔  f(xy)=0,
r_{xa}=r_xT_a,       c_{ay}=T_ac_y.
```

The shift equations must be present from the first solve. Persistent solutions may expose a
same-zero compiler; a finite unsatisfiable core may become a genuine zero-language
dimension obstruction.

The highest-yield source experiment is Carvalho's smallest cyclic-tag transducer. Compute
the rank and Stallings graph of its closed-path subgroup, classify the formal inverses used
by the fixed-loop proof, and test whether a rank-three positive basis or boundary-controlled
subgroup language survives. In parallel, search ternary finite-delay codes whose decoder is
total on all words, not merely correct on an intended subshift.

No further local fusion of the four displayed pairs should be attempted without identifying
which escape clause of `G3-O01` it uses.

## The rank-three binary wall: `M₃(2)`

### Rank census

`M₃(2)` remains unresolved. The binary pair can, however, be divided by rank without losing
the word problem.

| Rank profile | Reduction |
| --- | --- |
| `(3,3)` | immortal: every product is a unit |
| any rank `0` | immediately mortal |
| any rank `1` | decidable through order-at-most-three scalar recurrence zeros; [`R32-O01`](SALVAGE.md#r32-o01-rank-one-profile-collapse) |
| `(2,2)` | exact two-vertex square of `2 × 2` edges; [`R32-S02`](SALVAGE.md#r32-s02-two-plane-edge-square) |
| `(3,2)` | products of one third-order `2 × 2` return recurrence; [`R32-S01`](SALVAGE.md#r32-s01-split-return-normal-form) |

Thus two residues survive:

```text
rank (2,2): graph-constrained projective incidence on P¹(ℚ),
rank (3,2): mortality of {VAⁿU : n≥0},  A∈GL₃(ℚ).
```

The first already contains the dimension-two hard core. The generic reverse construction
[`R32-M01`](SALVAGE.md#r32-m01-generic-reverse-edge-compiler) places one rank-one test loop and
three invertible edges in a compatible two-plane square. Its basis adaptation and complete
all-path converse are formalized for `αβ≠0`. Only the two exceptional projective positions
remain: no checked three-dimensional OR gadget combines their finite disjunction into one
many-one instance. Conversely, no theorem removes every graph constraint from an arbitrary
rank-`(2,2)` pair. “Equivalent to `M₂(3)`” would therefore still be too strong.

The rank-`(3,2)` profile is the genuinely new artery. If `B=UV`, every binary word containing
`B` is governed exactly by

```text
M_n = VAⁿU ∈ M₂(ℚ).
```

The entries of `M_n` are algebraic linear recurrences of order at most three, but the problem
asks whether the semigroup generated by the infinite recurrence family contains zero. Skolem
decidability for each fixed entry does not decide products of returns with independently chosen
waits.

### ReturnSquare laboratory

[`R32-S03`](SALVAGE.md#r32-s03-returnsquare-normal-form) is the first completely normalized
rank-`(3,2)` family:

```text
A=diag(1,q,q²),       B=UV,
VAⁿU =
  [(c+1)q²ⁿ−1   qⁿ]
  [c              qⁿ].
```

The zero-wait return is an internal rank-one separator. Every other return is invertible, so
physical mortality is exactly one scalar bridge over positive waits. This removes the binary
word grammar entirely and leaves a rational projective orbit problem.

The family is now sharply fenced:

- `c=−1` is degenerate: `B²=0`;
- one-return zeros are exactly the resonances `c=−q⁻ⁿ`;
- two positive returns never vanish, by the discriminant square cage
  [`R32-O02`](SALVAGE.md#r32-o02-two-return-square-cage);
- `c≥0` is immortal;
- writing `c=−d`, the entire half-line
  `d > 1+(q−1)/q²` is immortal by the projective double-cone wall
  [`R32-D01`](SALVAGE.md#r32-d01-returnsquare-immortality-walls);
- a literal reversible push/pop replacement for the squaring rail requires at least four exact
  states, by [`R32-O03`](SALVAGE.md#r32-o03-reversible-stack-state-tax).
- adding a third singular `1,t,t²` mode still cannot implement reversible squaring, while two
  exact squaring checks collapse to blind scaling, by
  [`R32-O04`](SALVAGE.md#r32-o04-quadratic-pencil-verification-collapse).
- if `q` is a prime power, mortality occurs exactly at the one-return resonances, by
  [`R32-D02`](SALVAGE.md#r32-d02-prime-power-returnsquare-classification).

Thus every unclassified ReturnSquare instance has a base divisible by at least two distinct
primes; every nonresonant zero must use at least three positive returns in the bounded middle
negative strip. The one-base prime-power architecture is closed.

The obvious nonsemisimple escape is closed as well. A `1⊕J₋₁` ambient mode can realize the
exact parity-Collatz rails, but the rank-compatible branch is unique up to scalar and preserves
a nonzero line modulo seven. This is
[`R32-O05`](SALVAGE.md#r32-o05-jordan-parity-verifier-collapse).

ReturnConvert [`R32-M03`](SALVAGE.md#r32-m03-two-scale-return-conversion) exposed the missing
valuation direction. The amalgamated guard
[`R32-M04`](SALVAGE.md#r32-m04-amalgamated-valuation-guard) now closes the matrix-engineering
problem outright. In three exact modes it combines a rank-one internal separator, invertible
positive returns, legal-wait verification, and a permanent p-adic trap for every illegal wait.
The checked guarded normal form
[`R32-S04`](SALVAGE.md#r32-s04-guarded-return-normal-form) proves that arbitrary physical
mortality is exactly deterministic target reachability for one rational p-adic orbit.

That orbit is now localized further. In the shifted coordinate, each step is a variable-length
p-adic prefix decoder followed by one fixed fractional-linear map; on a branch, the reciprocal
residual updates affinely. This is
[`R32-S05`](SALVAGE.md#r32-s05-prefix-shift-and-affine-residual).
More decisively, [`R32-S06`](SALVAGE.md#r32-s06-resonance-localization) proves that every
nonresonant ready continuation strictly decreases the positive wait, while an overdeep tail is
poisoned. Every infinite ready chain therefore enters the equal-depth resonance shell
arbitrarily late.

The obvious rational-counter route is closed. By
[`R32-O06`](SALVAGE.md#r32-o06-rational-affine-wait-rail-rigidity), a reduced rational chart
cannot realize `a↦da+h` at infinitely many prime-power configurations unless the wait update is
the identity. The proof forces `P(λXᵈ)∣Q(X)`, then `d=1`, equal degrees, and finally a p-adic
contradiction for every nonzero shift `h`.

The global state has now been contracted again. By
[`R32-S07`](SALVAGE.md#r32-s07-decoded-residual-address-normal-form), the reciprocal center
displacement lies in one of pairwise disjoint rational p-adic spheres, and each sphere is the
image of the rational unit shell under one explicit Möbius inverse branch. Physical mortality
is exactly finite inverse-address membership of the terminal residual. Distinct branches share
no finite fixed point, so no single Möbius chart makes their interaction affine.

This address system has genuine rational nested dynamics: the checked period-three itinerary
uses waits `1,2,3`, with two consecutive resonant increases followed by nonresonant descent. The
first naïve periodicity conjecture is therefore false.

The first global arithmetic sieve is also exact.
[`R32-M05`](SALVAGE.md#r32-m05-cyclotomic-reset-or-cancellation-sieve) projectivizes the
primitive integer-pair recurrence and proves that every prime divisor of `pᵃ−1` either resets
the reduced point to one or is swallowed by the common reduction factor. The latter event is
not an untyped failure of a finite quotient: for every divisor `d ∣ pᵃ−1`, primitive reduction
swallows `d` exactly when the source residual is congruent to the terminal residual modulo `d`.
The remaining local-global escape is therefore repeated terminal shadowing at unbounded
cyclotomic orders.

[`R32-S08`](SALVAGE.md#r32-s08-terminal-defect-cocycle) separates two arithmetically distinct
normalization mechanisms. Outside the fixed prime support of `DL`, a common factor is swallowed
exactly when it divides both `pᵃ−1` and the terminal defect. Inside that fixed support, large
height collapse is already real: all three normalization factors of the checked period-three
orbit divide `DL`. A finite-nucleus proof must therefore normalize the fixed `S`-unit directions
before applying primitive-divisor growth; total gcd or ordinary height cannot be monotone.

[`R32-S09`](SALVAGE.md#r32-s09-complete-cancellation-law) removes the remaining ambiguity in
that split. For every prime `ℓ≠p`, the exact cancellation depth is

```text
min(vℓ(T(m,n)), vℓ(L(1−pᵃ)m)).
```

Fixed and novel cancellation are not separate algebraic phenomena: both are the intersection of
the terminal divisor with one displacement divisor. The distinction is dynamical. Outside fixed
support the displacement valuation is cyclotomic; at fixed primes it can also contain source
valuation. On a primitive source, however, determinant support bounds the cancellation actually
attained by `vℓ(DL(pᵃ−1))`.

[`R32-S10`](SALVAGE.md#r32-s10-logarithmic-wait-and-height-envelope) makes that bound effective.
Lifting the exponent proves logarithmic wait dependence at every fixed prime, including the
two-adic case. Globally, `|g|≤|DL||pᵃ−1|`. More importantly, a nonzero legal step obeys

```text
a ≤ log_p((|A|+|D|+|L|)H),
H′ ≤ (|A|+|D|+|L|)H.
```

Thus waits grow at most linearly with orbit time. This removes superlinear clock amplification
as a universality mechanism, but it does not yield a finite state space: exponential height and
linear counter growth remain possible.

[`R32-S11`](SALVAGE.md#r32-s11-primitive-factor-terminal-gate) now performs the first exact
local-global comparison. Let the primitive cyclotomic radical be the product of the distinct
prime factors of `Φ_a(p)` which do not divide `a`. If that radical exceeds

```text
(|A−L|+|D|)H,
```

then the current state is terminal or at least one exact-order prime survives reduction and
resets the next projective state to one modulo that prime. Conversely, if a nonterminal step
evades every such finite quotient, the entire primitive radical is at most the terminal defect
and hence at most this height envelope. The arithmetic residue is now exact: one needs either
finite-quotient separation or lower bounds for the squarefree primitive part of cyclotomic
values. Growth of `Φ_a(p)` alone does not suffice because repeated prime powers are discarded by
the radical.

[`R32-S12`](SALVAGE.md#r32-s12-exact-order-projective-automata) turns surviving factors into an
exact finite proof system. A primitive divisor `ℓ` of exponent `e` yields a transition automaton
on `ℙ¹(𝔽ℓ)⊔{cancelled}` whose labels are the `e` wait residues. On an actual primitive integral
step, `cancelled` is reached exactly when `ℓ` is swallowed by normalization; otherwise the
automaton follows the reduced rational state. A closed invariant containing the reset but not
cancellation is therefore a complete certificate against primitive terminal executions.

[`R32-S13`](SALVAGE.md#r32-s13-canonical-decoded-integral-lift) closes the normalization
direction needed to apply those certificates to the physical pair. Canonical rational
numerator-denominator coordinates are primitive, and a decoded target is a p-adic unit, so its
canonical denominator is prime to `p`. In the raw branch fraction

```text
N / (p^(sa)T),
```

the entire `p^(sa)` scale must therefore divide the common reduction factor. Removing it yields
exactly one `PrimitiveIntegralStep`; decoded executions lift step for step. A safe quotient
invariant now proves decoded unreachability and physical immortality without an independent
rational-cycle argument.

This mechanism is nonvacuous. For the checked rational period-three survivor, `ℓ=11` has exact
order five for base three, and all residue transitions collapse onto `{1,4,6,10}`. The terminal
ray is zero and cancellation is unreachable. Lean consequently excludes every primitive
integral terminal execution and, through the canonical lift, proves the physical pair immortal.
Reconnaissance also found many saturated quotients, so the remaining question is not whether
finite certificates exist or are sound, but whether some effective family is complete. The
modulo-eleven example owes its rank-one collapse to `11∣D`; parameter-divisor certificates and
genuinely projective primitive quotients should be analyzed separately.

The parameter-divisor branch is now uniform. If a primitive divisor also divides `D`, while
`A−L` and every `A−Lpʳ` over one period remain nonzero, all quotient transfers are rank-one
resets of the nonzero affine shell and the terminal residual is zero. This is an immediate
finite no-certificate. The condition is the clean group-theoretic exclusion
`A/L∉⟨p⟩⊆𝔽ℓ×`. The physical theorem uses the canonical terminal pair, so an unreduced raw
terminal presentation cannot make the certificate vacuous.

[`R32-S14`](SALVAGE.md#r32-s14-drift-divisor-certificate-classification) closes this subfamily
exactly. At a primitive drift divisor, *some* closed safe quotient invariant exists if and only
if the center avoids the scaled base-power orbit. If a residue hits the center, closure from the
reset forces either quotient annihilation or the terminal zero ray in one step; no smaller or
less obvious invariant can rescue the certificate. If the scale survives, the forbidden orbit
has exactly `e` elements and the classifier accepts exactly `ℓ−e` center residues. Thus large
primitive factors of small order kill most center classes, while `e=ℓ−1` leaves only the zero
center class. The test is executable in Lean and the modulo-eleven example is accepted by it.

[`R32-S15`](SALVAGE.md#r32-s15-finite-quotient-completeness) closes the missing global clause.
The zero-residue transfer is the rank-one reset with covector `(A−L,D)`, so its kernel is
exactly the terminal residual. Any invariant containing terminality therefore contains
cancellation one step later. Safe certificate existence is precisely cancellation
unreachability; terminal exclusion is redundant. This also kills ordinary synchronized
multi-prime products: every joint invariant excluding cancellation in either coordinate
projects to a cancellation-free invariant in each factor. A product cannot rescue any failed
factor. Further local-global progress must model what happens *through* primitive
renormalization, retaining swallowed-factor valuations instead of treating cancellation as an
absorbing reject state.

[`R32-S16`](SALVAGE.md#r32-s16-cancellation-blow-up-and-unbounded-depth) now computes that
renormalization exactly. Comparing the terminal-defect depth `t` with the cyclotomic
displacement depth `e` gives three exits: `t<e` forces one, `e<t` forces infinity, and `t=e`
retains the tangent ratio `[T₀+C₀:T₀]`. The exceptional divisor is surjective onto the entire
projective line. More strongly, no fixed congruence depth determines this exit, and one fixed
valid integral recurrence realizes every positive `3`-adic cancellation depth on primitive
inputs. Uniform finite-jet enrichment is therefore dead. The only possible finite nucleus is
orbit-specific: it must prove that the canonical reset orbit cannot visit arbitrarily deep
equal-depth collisions. The opposing universality program must make that one orbit do exactly
so.

[`R32-S17`](SALVAGE.md#r32-s17-normalized-tangent-cocycle) shows that collision is not an
exceptional terminal case. In coordinates

```text
v=(n,p^(sa)m−n),
```

consecutive primitive reductions obey an exact `2 × 2` matrix cocycle. Its determinant is
`DLp^(sa)(1−pᵇ)`, so after removing fixed parameter support every new common factor is again
cyclotomic for the next wait. Modulo such a factor the next collision is passage through one
explicit moving kernel line. The arithmetic obstruction is therefore recursive on the
exceptional divisor.

This also sharpens the height warning. The canonical rational period-three survivor lifts to a
nonzero projective tangent three-cycle, so no scalar tangent height can decrease on every
decoded step. All of its normalization is fixed-support, however. A finite-nucleus proof may
still exist after quotienting those finitely many `S`-unit directions; the remaining enemy is
novel cyclotomic normalization in the tangent cocycle.

[`R32-S18`](SALVAGE.md#r32-s18-fixed-support-localization-obstruction) performs that quotient
canonically. In the localization away from `D·L·p`, a tangent transfer is invertible exactly
when `1−pᵇ` is a unit. This clean separation does **not** leave a uniform finite nucleus: the
fixed guard `(5,2,29,1,1)` retains pairwise nonassociated cancellation factors
`1,3,3²,…` after localization away from five. Uniformity over all primitive inputs is therefore
dead. The remaining decidability claim must be orbit-specific to the canonical reset; the
opposing construction must force that one orbit, rather than freely chosen inputs, through
unbounded novel depth.

[`R32-S19`](SALVAGE.md#r32-s19-canonical-cyclotomic-collision-ladders) reaches that canonical
orbit. The product of primitive reductions is exactly the content of the composed tangent
image, but this identity supplies no descent: the transfer product can grow with the swallowed
content. More sharply, any chosen divisor of `pᵃ−1` can be installed as the complete first
novel reduction of a canonical reset, and one fixed reset orbit has four consecutive novel
reductions after fixed-support normalization. Endpoint-only budgets, first-collision bounds,
and parameter-uniform bounds are therefore closed. What remains is genuinely sequential:
either fixed parameters impose an effective bound, or compatible `p`-adic and cyclotomic
congruences synthesize arbitrarily long prefixes.

[`R32-S20`](SALVAGE.md#r32-s20-center-drift-parameter-lifting) identifies the local synthesis
law. With reset fixed, a center perturbation `ε` changes every homogeneous exit by the rank-one
vector `ε(m−n)(1,p^(sa))`. Perturbing by a multiple `q t` of an existing reduction factor
preserves `q` and moves the reduced exit affinely in the digit `t`; every visible moving-kernel
observer selects one unique digit. A fixed guard now carries five consecutive novel reductions,
with the fifth factor thirteen. Exact arithmetic continues the same compatible construction
through seventeen steps, but that longer evidence is not formalized. The live obstruction has
moved from local solvability to global coherence: prefix stability and visibility must persist,
and the compatible `(3,13)`-adic residue tower must contain a rational parameter rather than
only a profinite limit.

The surviving obligation is therefore a source theorem, or its negation: prove that this
countably branched rational address system can simulate universal deterministic computation
inside infinitely nested equal-depth resonance, or decide finite terminal-address membership by
controlling cyclotomic cancellation. No further punctuation, malformed-word, independently
selected wait, or rational affine-counter problem remains in this architecture.

### Live attacks

| Lane | Required move | Present obstruction |
| --- | --- | --- |
| Resonance arithmetic | Prove effective eventual periodicity of rational inverse addresses, or construct a rational nonperiodic resonance stack | A rational period-three nested orbit exists; every nonresonant continuation descends, but local p-adic symbolic freedom is complete |
| Amalgamated valuation guard | Compile a universal deterministic source into the resonant tail recurrence, or decide that recurrence | Matrix mortality is already equivalent to one deterministic orbit, but its remaining arithmetic is not covered by known p-adic dynamics |
| Irreducible cubic return pencil | Replace the split spectrum by a cubic companion action whose `2 × 2` return sequence has no fixed rail or target strip | A candidate still needs an internal low-rank return and an exact arbitrary-word normal form |
| Multi-prime ReturnSquare | Extend the rational-root support and finite walls from prime powers to bases with several prime factors | Mixed prime support permits roots not confined to one valuation ray |
| Cancellation-aware local-global sieve | Bound novel localized collisions for each fixed guard, or synthesize canonical prefixes of arbitrary length | [`R32-S20`](SALVAGE.md#r32-s20-center-drift-parameter-lifting) reduces each visible next collision to one affine parameter digit and checks five consecutive novel collisions; induction, persistent visibility, and rational realization remain |
| Valuation and cone dynamics | Extend the signed-cone pullback or a `p`-adic invariant across the remaining middle strip or a new pencil | Cancellation at poles and between spectral modes destroys naive monotonicity |
| Same-zero return surgery | Change nonzero return values while preserving the zero semigroup, thereby evading exact Hankel taxes | No general same-zero minimization theorem exists; every surgery needs its own arbitrary-product converse |
| Exceptional reverse compiler | Absorb the finite `αβ=0` disjunction into one three-dimensional many-one instance | The generic all-path compiler is complete; dimension three has no evident OR operation |

The highest-value lunge is now orbit-specific cancellation arithmetic. The matrix compiler,
all-word converse, wait decoder, rational address grammar, and local blow-up are complete;
nonresonant dynamics, rational affine counter rails, ordinary quotient products, and uniform
fixed-jet and fixed-support-localized uniform nuclei are closed. The next useful mathematics is
an induction for the visible affine parameter digits, a proof that its compatible residue tower
has or lacks rational points, an effective per-instance novel-depth bound, or a transfer from
that dichotomy to a broader class of three-mode return recurrences.

The strategic boundary is now clear. The easy layer consisted of finding and repairing missing
finite compilers. `M₃(2)` asks whether one low-dimensional recurrence family can store
unbounded, independently selectable history without paying another state or generator. That is
the same synchronization tax seen at the neighboring hard cells, stripped of parser
accidents.

## The dimension-two wall: `M₂(3)`

### Status and exact hard core

The public-literature audit through 2026-07-24 found neither a decision algorithm nor an
undecidability proof for `M₂(3)`. The case is equivalent to point-to-point reachability on
`P¹(ℚ)` under two rational Möbius transformations; the reusable reduction is
[`D2-S01`](SALVAGE.md#d2-s01-projective-hard-core).

Let `X₁⋯Xₙ=0` be a mortal word of minimal positive length over `2×2` matrices. Its first and
last factors are singular: an invertible endpoint could be cancelled. Every interior factor is
nonsingular. Indeed, if an interior factor is `uvᵀ`, then

```text
0 = P(uvᵀ)Q = (Pu)(vᵀQ)
```

forces either `Puvᵀ=0` or `uvᵀQ=0`, producing a shorter mortal word.

For an input of at most three matrices this leaves one unresolved rank pattern: two
nonsingular matrices `A,B` and one nonzero singular matrix `R=cr`. Every minimal witness then
has the form

```text
R W R,       W ∈ {A,B}*,
```

and

```text
R W R = c(rWc)r.
```

Consequently,

```text
M₂(3)  ≡  given A,B ∈ GL₂(ℚ), r≠0, c≠0, decide ∃W∈{A,B}*: rWc=0.
```

After projectivization this asks whether the submonoid generated by `A,B` sends `[c]` to
`P(ker r)`. If `rc=0`, the empty interior already gives `R²=0`; otherwise a rational change of
basis turns the condition into a zero in one fixed matrix corner. Clearing denominators and
independently rescaling the three generators preserves zero products, so the rational incidence
problem and integer mortality are computably interreducible.

The reduction has only one incidence instance. Multiple endpoint pairs arise for larger
families with several singular generators, not in the hard three-generator case.

### Established and provisional decidable strata

The established baseline consists of two-generator `2×2` mortality, the at-most-one-nonsingular
preprint result, the `GL₂(ℤ)` reachability algorithms, and one-dimensional integral-affine
reachability. The project-derived extensions are indexed with their exact evidence and scope:

- projectively unimodular pairs:
  [`D2-D01`](SALVAGE.md#d2-d01-projectively-unimodular-stratum);
- groups preserving an unordered projective pair:
  [`D2-D02`](SALVAGE.md#d2-d02-invariant-pair-stratum);
- affine maps with a common rational multiplier:
  [`D2-D03`](SALVAGE.md#d2-d03-common-multiplier-stratum);
- rational subsets of one single-base affine group:
  [`D2-D04`](SALVAGE.md#d2-d04-single-base-affine-stratum);
- prescribed translated-letter count:
  [`D2-D05`](SALVAGE.md#d2-d05-prescribed-translation-count);
- affine pairs with a private multiplier prime outside one endpoint shell:
  [`D2-D06`](SALVAGE.md#d2-d06-private-prime-peeling);
- bounded affine families with cooriented valuation vectors:
  [`D2-D07`](SALVAGE.md#d2-d07-bounded-valuation-orthants).

`D2-D01` and `D2-D05`–`D2-D07` have passed independent project audits. The invariant-pair,
common-multiplier, and single-base records remain reported research stock, not publication
theorems.

Simultaneous triangularization alone is not a solved stratum. It yields rational affine
reachability

```text
z ↦ a_i z+b_i,
```

whose general two-map case remains part of the wall. The provisional common-multiplier and
single-base theorems and the audited valuation strata cover substantial subfamilies but do not
settle every mixed multiplicative direction.

### Exact unresolved residue

Two qualitatively different classes remain after the preceding tests.

#### Mixed-prime affine systems

These have a common rational fixed point but genuinely independent multiplier valuations.
After affine normalization, every non-elementary pair has the form

```text
F(z)=az,      G(z)=bz+1.
```

Its words obey the monotone exponent-path theorem
[`D2-S02`](SALVAGE.md#d2-s02-monotone-affine-path-form). A prescribed number of `G` letters is
decidable by rational-base carries, and a private prime often determines that number directly.
Bounded cooriented valuation families are finite-state even when their slopes are
multiplicatively independent.

The benchmark

```text
z ↦ (2/3)z+1,       z ↦ (3/5)z+1
```

is therefore no longer wholly opaque. It is conjugate to

```text
F(z)=(2/3)z,      G(z)=(3/5)z+1.
```

Private-prime tests decide every endpoint pair outside

```text
v₅(3−x)=0,      v₂(6y−15)=0.
```

Inside that shell, every maximal shell-preserving prefix is governed by

```text
T_m(u)=(1+3u(2/3)^m)/5,
v₅(u)=v₅(T_m(u))=0.
```

The exact scope and the remaining infinite-exit seam are
[`D2-M01`](SALVAGE.md#d2-m01-benchmark-critical-shell). The general affine residue still
includes pairs with no private prime, no bounded invariant interval, and incompatible valuation
signs.

#### Non-elementary projective systems

Here the generators have no common rational eigenline and preserve no unordered pair of
projective points. They are not projectively unimodular and need not generate a free monoid.
The problem becomes intersection of the positive rational subset

```text
⟨A,B⟩⁺
```

with a rational parabolic coset carrying the source point to the target.

These two residues should be attacked separately. A theorem for the affine class need not
touch the non-elementary case.

### False shortcuts

| Temptation | Failure |
| --- | --- |
| Apply fixed-target matrix membership | the incidence variety contains matrices of unbounded determinant |
| Invoke flat rational-subset algorithms | `(A+B)*` permits unbounded alternation and need not be flat |
| Declare triangular systems decidable | rational affine reachability remains unresolved outside special strata |
| Treat arbitrary words as one recurrence | word order is stored by a two-state rational series, not one exponent |
| Use a free subgroup normal form | the input generators may satisfy relations such as `A³=B²` |
| Import the standard PCP encoding | two independent free-word tapes do not embed in `2×2` complex matrices |
| Track only determinant or Smith form | equal arithmetic invariants can have different projective orbits |
| Assume projective height descends | determinant-growing words may act projectively as the identity |
| Invoke a general module `S`-unit algorithm | the arbitrary three-prime case leads to open linear-exponential systems, and forgetting the monotone path destroys useful structure |

These are exclusion tests for future proposals. Any attack relying on one of them must identify
the additional hypothesis that repairs the failure.

### Pre-mortem: imported structural principles

The following is a research-prior allocation, not evidence for either outcome. Condition on
`M₂(3)` being resolved by an imported structural theorem rather than a local extension of
mortality machinery:

```text
Pr(decidable | imported resolution)   ≈ 0.80
Pr(undecidable | imported resolution) ≈ 0.20.
```

| Primary source of the decisive lemma | Credence | Outcome allocation |
| --- | ---: | ---: |
| `S`-arithmetic geometry, Bruhat–Tits trees, reduction theory | 21% | 20% decidable, 1% undecidable |
| Numeration systems, continued fractions, finite-state transducers | 17% | 12% decidable, 5% undecidable |
| Metabelian groups, Laurent modules, `S`-unit equations | 15% | 13% decidable, 2% undecidable |
| Rational subsets, Bass–Serre theory, parabolic-coset algorithms | 12% | 10% decidable, 2% undecidable |
| `SL₂` trace algebras, character varieties, Markoff descent | 9% | 8% decidable, 1% undecidable |
| Arithmetic dynamics, height gaps, Subspace-Theorem methods | 8% | 7% decidable, 1% undecidable |
| Verification, well-structured systems, affine-loop acceleration | 6% | 5% decidable, 1% undecidable |
| Profinite topology, congruence separation, automatic structures | 5% | 5% decidable |
| FRACTRAN, Collatz systems, automaton-semigroup universality | 6% | 6% undecidable |
| Other structural sources | 1% | predominantly undecidable |

The percentages are coarse hypothesis weights. They are intended to force diversity in the
next prompt battery, not to rank theorem credibility.

### Independent attack lanes

Dispatch each lane as a standalone investigation. It must conduct its own deep literature
review, attack the full incidence problem rather than merely survey it, state the strongest
proved import it finds, and identify an explicit falsifier for its proposed mechanism. Synthesis
comes only after the independent reports return; shared vocabulary must not collapse genuinely
different hypotheses into one generic prompt.

#### 1. Adelic parabolic reduction

Let `S` be the primes appearing in denominators and nonunit determinants. Study the simultaneous
action on the real hyperbolic plane and the Bruhat–Tits trees `T_p`, `p∈S`. The desired theorem
is an effective finite cone-type decomposition relative to a rational parabolic, with the
unbounded part carried by decidable Busemann counters. The critical obstruction is
synchronization across several primes.

The first falsifier is a pair whose simultaneous Busemann coordinates simulate an unrestricted
two-counter system. The first positive certificate is a bounded-cancellation or induction
theorem reducing one bad prime at a time.

#### 2. Redundant projective numeration

Represent rational points by continued fractions, Stern–Brocot addresses, or redundant
signed `S`-adic expansions. Search for a representation in which both Möbius generators have a
common finite carry nucleus. Canonical expansions are not privileged; the single-base pointed
expansion for `BS(1,q)` is evidence that annotation can turn nonregular arithmetic into a
regular language.

For the affine benchmark, the first target is narrower: decide whether the guarded maps

```text
T_m(u)=(1+3u(2/3)^m)/5
```

have a finite redundant base-`5` carry nucleus that also recognizes accepting shell exits. For
the non-elementary residue, compare reachable carry-state growth for ordinary continued
fractions, slow continued fractions, Stern–Brocot paths, and redundant multi-prime expansions.

#### 3. Characteristic-zero affine modules

For triangular systems, express the translation component as a module element over the
multiplicative slope group. The target theorem is decidability of cyclic-coset reachability in
a rank-one characteristic-zero module-by-abelian group generated by two affine maps. Minimal
`S`-unit relations, Laurent-module normal forms, or effective semilinearity are the likely
invariants.

The unresolved critical shell of the `(2/3,3/5)` pair is the benchmark. Generic endpoints are
already peeled by `D2-D06`; a method that cannot decide the shell has not crossed the affine
residue.

#### 4. Rational subsets and relative normal forms

Seek an algorithm deciding intersection of a positive rational subset of a two-generated
subgroup of `PGL₂(ℚ)` with a rational parabolic coset. Candidate imports are Bass–Serre
decompositions, relative automatic structures, and rational-subset closure theorems for graphs
of groups with affine edge or vertex groups.

This lane should target arbitrary regular control languages. Success only for bounded
alternation reproduces the existing flat theory.

#### 5. Trace or height descent

Exploit the dimension-four algebra generated by two `2×2` matrices, Fricke trace identities,
and Nielsen transformations. Enlarge trace data by the boundary coefficients

```text
rc, rAc, rBc, rABc
```

and search for a mutation or height that strictly descends for every minimal zero word outside
an elementary locus. Arithmetic-dynamics variants may instead prove a computable bound on
normal-form length.

Raw word length is not a lawful height: relations can make long words represent short group
elements.

#### 6. Exact symbolic saturation and finite obstructions

Run backward saturation from the target using cones, valuation vectors, residue classes, and
affine lattices. A successful well-structured formulation must decide exact reachability, not
only coverability. In parallel, test whether no-instances are separated by a finite congruence
quotient. Congruence separation would provide enumerable finite certificates for “no.”

Persistent local-global failures modulo every tested modulus would falsify the profinite route.

#### 7. Valuation universality

For undecidability, encode configurations in prime valuations or disjoint `p`-adic cylinders.
The two Möbius generators must be total, so illegal instructions require irreversible geometric
traps rather than external guards. A valid proposal must include the arbitrary-word converse:
every accidental incidence must decode to a legal computation.

Single-base affine encodings and common-multiplier digit systems are excluded by the decidable
strata above. A plausible construction must use mixed valuation directions or a non-elementary
projective action.

### Discriminating signals

- Arbitrary regular control favors rational subsets, buildings, numeration, or module automata.
- A theorem for any finite generator set favors adelic or automatic structure over
  two-letter combinatorics.
- A theorem confined to two named generators favors trace descent, continued-fraction
  transducers, or a two-map universality construction.
- Nonelementary complexity with a finite-state core favors building automata, `S`-unit
  equations, or Presburger saturation.
- Semilinear no-certificates favor affine modules or verification.
- Finite-modulus no-certificates favor profinite separation.
- A computable witness bound favors height, Diophantine, or trace descent.
- A virtually-solvable/non-elementary dichotomy favors arithmetic dynamics.
- An undecidability construction with several prime determinants favors valuation storage.

### Composite proof shapes

The modal decidability route combines the adelic, numeration, and rational-subset lanes:

1. encode the action at every bad prime by finitely many cone types, Busemann coordinates, and
   carry states;
2. construct an effective regular or automatic normal form closed under rational control and
   parabolic cosets;
3. recognize the coset of transformations carrying the source point to the target and decide
   intersection.

The principal fallback first solves the mixed-prime affine residue by a characteristic-zero
Laurent-module theorem, then uses a normal-form height or cancellation theorem on the
non-elementary residue. The modal undecidability route instead requires a genuinely multi-prime
`p`-adic transducer with invariant configuration cylinders, irreversible traps for illegal
choices, and a complete arbitrary-word converse.

The highest-value intersection is

```text
S-arithmetic parabolics
+ annotated numeration systems
+ rational-subset automata.
```

The concrete question is whether the pointed-expansion phenomenon for one affine base extends
to a synchronized finite family of primes, or whether that synchronization already supports
universal computation.

## Execution order

1. Construct an open-tail binary two-state source invariant or solve the mixed cube-root
   punctuation incidence equations. Use formalized `M4-O02`–`M4-O04` to reject every exact
   two-private-state clock, finite closed-token source, and exact internal/final recoloring
   before appendant search.
2. Use formalized `MM-O01`, `G3-O01`, `MM-O03`, and `MM-O04` to reject exact packings, macros,
   and bridges without conflating their scope with solvability preservation.
3. Prove or refute the setter candidate's projective avoidance property, construct a
   five-state same-zero binary root, or find a constant-state scheduled delimiter fusion.
   Treat fixed-width-three universality as a separate source theorem. Reopen `MM-C04` only for
   a physically different six-state family.
4. Treat `MM-O08` and `MM-O11` as formally closed exact-family obstructions. Search for
   `M₉(2)` only through a changed physical pair, changed nonzero behavior, or a nonlinear
   compiler.
5. Run the `M₃(4)` program on three separate tracks: shift-equivariant point-line synthesis,
   the closed-path subgroup of Carvalho's smallest transducer, and total ternary
   synchronization codes. Do not collapse their distinct proof obligations into one prompt.
6. Formalize `D2-S02` and `D2-D05`–`D2-D07`, then attack the guarded `5`-adic critical shell
   with a finite carry nucleus and a counter-simulation falsifier in parallel. Keep the
   non-elementary lanes independent: adelic cone types, parabolic rational subsets,
   trace/height descent, finite-obstruction saturation, and valuation universality.
7. Synthesize the returned attacks by the discriminating signals above; do not average
   incompatible hypotheses into one generic mortality prompt.

These are research programs, not consequences of the present theorem.
