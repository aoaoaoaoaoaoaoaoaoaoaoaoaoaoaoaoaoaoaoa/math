# Formal Verification

The Lean development verifies the source theorem and both matrix compilers

```text
four-tile terminal equation
  ↔ restricted tag halting
  ↔ corrected binary five-pair PCP
  ↔ four-generator GPCP
  ↔ mortality of the emitted five 3 × 3 integer matrices;

four-tile terminal equation
  ↔ scalar zero reachability for three 4 × 4 integer matrices
  ↔ mortality of the emitted four 4 × 4 integer matrices;

four-tile terminal equation
  ↔ scalar zero reachability for two 6 × 6 integer matrices;

for each fixed deletion width β:
four-tile terminal equation
  ↔ scalar zero reachability for two (β+2) × (β+2) integer matrices;

mortality of the emitted five 3 × 3 integer matrices
  ↔ mortality of two 10 × 10 integer matrices
  ↔ mortality of two (10+n) × (10+n) integer matrices.
```

It does not assume Neary's defective terminal-pair converse or Rote's long-block repair.

## Checked Scope

For deletion width `β`, body `q`, rules `b ↦ b` and `c ↦ q ++ [b]`, and initial queue
`q.drop (β−1) ++ [b]`, Lean proves under

```text
2 < β,    β−1 ≤ q.length,    β−1 ∣ q.length
```

that a word over Neary's four ordinary labels satisfies

```text
upper(w) ++ 10^β = lower(w)
```

if and only if the restricted tag system halts. The forward theorem accepts an arbitrary label
word. A zero-run automaton forces exact deletion-width blocks; prefix cancellation turns the
decoded history equation into lawful tag steps and stops at the first short queue.

The development also checks the fresh-marker fifth pair, fixed-length binary recoding,
primitive terminality, the ternary word-pair representation, the exact integer generators, and
the mortality converse for every nonempty word over all five labels. The four ordinary matrices
are nonsingular and upper triangular. The fifth is nonzero and has rank one over `ℚ`.

For the `4 × 4` compiler, Lean checks the side-separating change of basis, agreement of each
rule/erasure pair on the complete upper-word plane, and the explicit four-dimensional paired-role
representation. A right-to-left transducer decodes every arbitrary control word, and a constructive
surjectivity theorem encodes every four-role word. The three control matrices have common first
column `e₁`, and the toggle is an explicit permutation matrix. Adding the nonzero rank-one matrix
`CL` gives four integer matrices; the mortality converse covers every number and placement of
separators without assuming that control products are invertible. The two data controls are
singular; the toggle is an invertible permutation matrix.

For the `6 × 6` scalar compiler, Lean checks both explicit integer generators and a total
two-bit decoder on the complete binary free monoid. Complete pairs emit the four source roles;
an odd final bit preserves the coefficient. The decoder is surjective, the empty coefficient
is nonzero, and transposition plus word reversal gives two generators with common first column
`e₁`. The terminal equation is therefore equivalent to scalar zero reachability under both the
free-monoid and nonempty free-semigroup conventions.

For the scheduled binary compiler at deletion width `β`, Lean checks two explicit
`(β+2) × (β+2)` matrices. The input bit selects the tag letter; its position modulo `β`
selects deletion or rule semantics. A total decoder assigns a role to every bit, and the
coefficient identity holds for every binary word over every commutative ring. Reversed stroke
encoding is surjective onto every tile history. If a coefficient vanishes, the terminal-match
normal form forces a complete tile history, so `β` divides the binary-word length. At width
three and nonempty body, a symbolic `5 × 5` Hankel minor is nonsingular. Every exact rational
representation of the same series therefore has at least five states, matching the native
five-state representation.

For the `10 × 10` mortality compiler, Lean first checks a complete prefix transducer for the
code `0, 100, 101, 110, 111`. Its block-row theorem covers every binary word and every starting
prefix state. The word `00` synchronizes all four states, so mortality of the twelve-state
binary realization is equivalent to mortality of the normalized five-matrix source. Two shared
rows place both binary generators in a common ten-dimensional image. Explicit integral
embedding and retraction matrices prove the exact restriction and its converse, including any
new zero created by restriction. A generic zero-block theorem then preserves nonempty-word
mortality in every dimension `10+n`.

## Audited But Unformalized

The latest `M₅(3)` delimiter attack yielded four audited records:

| Record | Formalization obligation |
| --- | --- |
| [`MM-O06`](SALVAGE.md#mm-o06-pure-power-punctuation-obstruction) | common image and kernel of the lifted paired data, fixed-vector extraction, and contradiction with a contextual pure-power separator |
| [`MM-O07`](SALVAGE.md#mm-o07-setter-parameter-rigidity) | boundary alignment forces `r=t/μ`; verify the rejected benchmark coefficient |
| [`MM-M03`](SALVAGE.md#mm-m03-five-state-setter-punctuation) | explicit setter matrices, delimiter powers and ranks, regular decoder, and `S²A_cS³=λC̃L̃` |
| [`MM-S01`](SALVAGE.md#mm-s01-square-run-projective-normal-form) | invariant square-run plane, invertible `2 × 2` transfer, Möbius normalization, rank-one fracture grammar, and equivalence with pole avoidance |

The candidate proves only the halting-to-mortality direction. Its converse requires a theorem
that every nonterminal projective orbit avoids every pole. No such theorem is formalized or
assumed. The exact reconstruction and promotion boundary are recorded in
[`audits/m53-setter-projective-2026-07-24.md`](audits/m53-setter-projective-2026-07-24.md).
Formal promotion and the avoidance decision are tracked in
[#6](https://github.com/aoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoaoa/math/issues/6).

The `M₄(3)` attack produced one independently checked compiler and four independently checked
obstructions that are not yet Lean declarations:

| Record | Formalization obligation |
| --- | --- |
| [`M4-C01`](SALVAGE.md#m4-c01-two-state-pushout-compiler) | generic two-state pushout, total suffix decoder, reset-letter rank classification, and fixed-anchor mortality equivalence |
| [`M4-O01`](SALVAGE.md#m4-o01-exact-toggle-fusion-leaves-an-immortal-core) | exact contextual toggle identities imply an invertible common-plane restriction |
| [`M4-O02`](SALVAGE.md#m4-o02-two-private-state-phase-signature) | two-dimensional quotient phase ratios are constant or two-periodic; instantiate the Neary signature |
| [`M4-O03`](SALVAGE.md#m4-o03-closed-serialization-collapse) | finite closed-token substitution empties exactly when its reachable dependency graph is acyclic |
| [`M4-O04`](SALVAGE.md#m4-o04-exact-internal-final-code-defect) | binary morphism defect forces commuting upper images, contradicting the macro source |

The odd-phase macro cut [`M4-S01`](SALVAGE.md#m4-s01-odd-phase-macro-cut) remains reported.
Lean already defines the relevant phase residues and Table 2 tracks, but no theorem yet proves
the even-track invariant through every reachable queue or the induced macro solvability
equivalence. The direct first-return obstruction [`M4-O05`](SALVAGE.md#m4-o05-direct-two-state-first-return-recoding)
also remains reported. Neither claim enters the checked theorem ledger.

No `M₄(3)` undecidability theorem follows from the present corpus. The missing source is an
undecidable binary two-state controlled scalar system, or a matrix-level open-residue compiler
with a complete arbitrary-word converse.

## Modules

| File | Responsibility |
| --- | --- |
| `MatrixSemigroup.lean` | shared word semantics, mortality transports, common-image restriction, transposition, and zero padding |
| `TagQueue.lean` | tag steps and generic history soundness |
| `NearyEncoding.lean` | four ordinary tiles, synchronization, source equivalence, and composed reductions |
| `MarkedTerminal.lean` | fresh marker, primitive terminality, and binary recoding |
| `TernaryEncoding.lean` | injective nonzero ternary representation |
| `PCPEncoding.lean` | `3 × 3` word-pair morphism and equality entry |
| `TerminalTile.lean` | arbitrary rank-one chains and fracture at every separator |
| `TerminalReduction.lean` | rational and integer fixed-boundary mortality compiler |
| `TerminalSource.lean` | generic primitive extraction and GPCP bridge |
| `PairedCompression.lean` | side-normal representation, paired-role compression, and arbitrary-word decoding |
| `PairedMortality.lean` | common-column mortality converse and exact integer `4 × 4` family |
| `PairedBinary.lean` | total two-bit decoder and exact six-state scalar representation |
| `ScheduledBinary.lean` | fixed-width clock compiler, total decoder, and malformed-word converse |
| `ScheduledBinaryRank.lean` | exact width-three rank-five certificate and universal exact-state lower bound |
| `WeightedTransducer.lean` | deterministic matrix transducers and the arbitrary-word block-row theorem |
| `PrefixMortality.lean` | complete prefix decoder, twelve-state realization, and ten-state common-image restriction |
| `LintAudit.lean` | package-wide default mathlib environment lint |
| `AxiomAudit.lean` | transitive axioms of publication-facing declarations |
| `Undecidability/UniversalMachine.lean` | fixed verified two-tape interpreter for mathlib code halting |
| `Undecidability/CyclicTag.lean` | two-tag semantics and the one-hot cyclic-tag simulation |
| `Undecidability/Tracks.lean` | typed fixed-stride track serialization and recovery |
| `Undecidability/TagExecution.lean` | exact finite executions and sliced-track recovery |
| `Undecidability/NearyCompiler.lean` | exact Table 2 words, tracks, padding, and arithmetic envelope |
| `Undecidability/NearySimulation.lean` | traversal semantics of raw, bit, epsilon, and halting objects |
| `Undecidability/NearyData.lean` | garbage calculus, token invariant, and ordinary cyclic pulses |
| `Undecidability/NearyProblems.lean` | canonical `Fin 4` and `Fin 5` target instances |
| `Undecidability/PairedProblems.lean` | canonical four-matrix target instance and structural promises |
| `Undecidability/BinaryProblems.lean` | canonical structured `Z₆(2)` instance |
| `Undecidability/PrefixProblems.lean` | canonical `M₁₀(2)` instance and all zero-padded dimensions |
| `Undecidability/Problems.lean` | encoded source and target decision predicates |

## Principal Declarations

| Claim | Lean declaration |
| --- | --- |
| History equation implies halting | `tagHaltsFrom_of_history` |
| Terminal equality forces deletion blocks | `tileHistory_of_terminal_match` |
| Four-tile equality iff tag halting | `terminal_match_iff_tagHaltsFrom` |
| Corrected five-pair PCP iff tag halting | `nearyPCP_solvable_iff_tagHaltsFrom` |
| Primitive solutions end in tile five | `nearyPCP_primitive_terminal` |
| Four-generator GPCP iff tag halting | `nearyGPCP_solvable_iff_tagHaltsFrom` |
| Nonempty-witness GPCP iff tag halting | `nearyGPCPPlus_solvable_iff_tagHaltsFrom` |
| Five integer matrices mortal iff tag halting | `nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom` |
| Arithmetic-envelope specialization | `NearyArithmeticEnvelope.mortality_iff_halts` |
| Four ordinary matrices are nonsingular and triangular | `nearyMortality_ordinary_det_ne_zero`, `nearyMortality_ordinary_upperTriangular` |
| Exceptional matrix is nonzero and rank one | `nearyMortality_terminal_ne_zero`, `nearyMortality_terminal_rank_eq_one` |
| Rule and erasure matrices agree on the upper-side plane | `rule_erase_agree_on_upperSide` |
| Every compressed word realizes its decoded four-role word | `pairedProduct_mulVec_column`, `pairedCoefficient_eq_sideCoefficient` |
| Every four-role word has a compressed encoding | `decodePairedWord_surjective` |
| Three-matrix scalar zero iff the terminal equation | `paired_zero_iff_terminal_match` |
| Four integer matrices mortal iff the terminal equation | `pairedMortalityFamily_int_mortal_iff_terminal_match` |
| Canonical `M₄(4)` instance mortal iff tag halting | `nearyMortality44_mortal_iff_tagHaltsFrom` |
| Three control matrices have common first column | `nearyMortality44_control_fixes_anchor` |
| Toggle control is a permutation matrix | `nearyMortality44_toggle_eq_permMatrix` |
| Fourth matrix is nonzero and rank one | `nearyMortality44_separator_ne_zero`, `nearyMortality44_separator_rank_eq_one` |
| Every binary word has the exact six-state coefficient | `pairedBinaryRow_wordProduct`, `pairedBinaryCoefficient_eq_sideCoefficient` |
| Every four-role word has a two-bit encoding | `decodePairedBinary_surjective` |
| Canonical structured `Z₆(2)` instance iff tag halting | `nearyScalarZero62_hasZero_iff_tagHaltsFrom` |
| Free-monoid `Z₆(2)` instance iff tag halting | `nearyScalarZero62_hasZeroStar_iff_tagHaltsFrom` |
| Both `Z₆(2)` generators fix `e₁` | `nearyScalarZero62_fixes_anchor` |
| Every scheduled binary word has the decoded source coefficient | `scheduledRow_wordProduct`, `scheduledCoefficient_eq_sideCoefficient` |
| Every tile history has a scheduled binary encoding | `decodeScheduled_historyCode` |
| A scheduled zero has no incomplete clock cycle | `decodeScheduled_is_tileHistory_of_coefficient_zero`, `scheduledCoefficient_zero_length_dvd` |
| Scheduled scalar zero iff the terminal equation and tag halting | `scheduledBinary_zero_iff_terminal_match`, `scheduledBinary_zero_iff_tagHaltsFrom` |
| Width-three scheduled series has a nonsingular `5 × 5` Hankel minor | `scheduledWidthThreeHankel_det_ne_zero` |
| Every exact width-three rational realization needs five states | `scheduledWidthThree_exact_state_lower_bound`, `scheduledWidthThree_native_state_card`, `scheduledWidthThree_native_represents` |
| Every binary prefix-machine word has one decoded block per row | `prefixMachine_run`, `WeightedTransducer.wordProduct_apply` |
| Prefix-machine mortality iff five-matrix mortality | `prefixMachine_mortal_iff_normalized` |
| Both prefix generators share the ten-dimensional image | `prefixProjection_generator` |
| Ten-state mortality iff prefix-machine mortality | `restrictedPrefixGenerator_mortal_iff_prefixMachine` |
| Canonical `M₁₀(2)` instance mortal iff tag halting | `nearyMortality102_mortal_iff_tagHaltsFrom` |
| Every zero-padded `M₁₀₊ₙ(2)` instance iff tag halting | `nearyMortality10Plus_mortal_iff_tagHaltsFrom` |
| Mathlib code halting has a verified `TM2` interpreter | `exists_universalTM2` |
| Two-tag executions reach their cyclic firing phase | `CyclicTag.reaches_firing_phase` |
| A woven compiler word emits its prescribed track | `read_wholeAppendant_track` |
| One arbitrary ordinary cyclic pulse is simulated | `read_next_dataBit` |

## Logical Foundation

Lean checks proof terms in dependent type theory with inductive and quotient types and an
impredicative, proof-irrelevant `Prop`. Mathlib supplies proved definitions and lemmas; it is not
a second proof engine. Tactics such as `simp` and `omega` produce terms that Lean's kernel checks.

For every publication-facing theorem, `#print axioms` reports only:

```text
propext
Classical.choice
Quot.sound
```

These provide propositional extensionality, ordinary classical choice, and quotient soundness.
The project declares no axiom and uses no `sorry`, `admit`, `unsafe`, `partial`, `native_decide`,
external declaration, or unverified proof certificate.

The operational trusted computing base comprises the Lean kernel implementation, executable,
runtime, operating system, hardware, and the correctness of the formal specification. Parsers,
elaborators, tactics, and mathlib lie outside the logical trusted core because the kernel checks
their resulting terms.

## External Boundary

The complete universality chain is not yet formalized. On its upstream side, Lean now starts
from mathlib's theorem that code halting is noncomputable, constructs a verified universal `TM2`
interpreter, and proves the complete one-hot simulation from two-tag systems to cyclic-tag
systems. A computable reification of the fixed interpreter as a finite machine and the
finite-machine-to-two-tag compiler remain open.

On Neary's side, Lean defines the exact Table 2 tracks and their computable padding. It proves
that the whole `c`-appendant has length `βs`, ends in `b`, induces the required initial queue, and
inhabits the arithmetic envelope. Fixed-stride execution then verifies every raw, epsilon, zero,
ordinary-one, and distinguished-one object. The semantic data layer permits arbitrary garbage
prefixes and proves that every nonhalting cyclic-tag pulse produces the correct data update while
preserving the garbage reserve. The initial-track execution, distinguished halting cascade, and
global no-spurious-halting converse remain open. The chosen congruent padding gives

```text
q.length = (xβ + 1)(β−1),
```

so every compiler output used by the reduction inhabits `NearyArithmeticEnvelope`. The envelope
is deliberately broader than the exact Table 2 output family. This is the Neary padding
corollary used by the publication: it follows from the selectable padding in Neary's
construction, not from the bare statement of Lemma 9.

Thus all source-to-matrix equivalences and a substantial proper prefix of the universality
compiler are machine-checked. The exact encoded results currently end at
`nearyMortality44_mortal_iff_tagHaltsFrom`,
`nearyScalarZero62_hasZero_iff_tagHaltsFrom`, and
`nearyMortality10Plus_mortal_iff_tagHaltsFrom`. Their final no-decider theorems remain
conditional on a computable source reduction. The mathematical undecidability conclusions use
Neary's peer-reviewed Lemma 9 at that external boundary. CHHN's frontier transports and
bibliographic priority claims are external to Lean and are not dependencies of the direct
compilers.

The scheduled compiler introduces a separate source-width seam. Neary's published construction
sets `β = 10p`, where `p` is the simulated cyclic-tag program period. The fixed-width audit found
no universality theorem for the required binary deletion-width-three family. Cocke and Minsky
fix deletion width two only by allowing the alphabet to grow; the adjacent binary width-three
class remains unresolved in the located literature. The width-three Lean theorem is therefore
a conditional five-state reduction and an exact-rank result, not an established undecidable
cell.

## Prior Formalizations

The public Lean corpus was audited on 2026-07-22 for an executable reduction chain that could
replace that external boundary. A usable component had to provide a computable translation,
the required halting equivalence, a compatible license, and no admitted simulation theorem.
Name-level overlap was not enough.

| Development | Audited revision | Result | Reuse decision |
| --- | --- | --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/809c3fb3b5c8f5d7dace56e200b426187516535a/Mathlib/Computability) | `809c3fb3` (`v4.12.0`) | Proves noncomputability of code halting and interprets partial-recursive code by Turing machines | Adopt the code-halting theorem. Its finite-support TM translations contain proof-level choices and do not themselves emit a computably encoded finite machine. |
| [Wolfram TuringMachine](https://github.com/WolframInstitute/TuringMachine/tree/ff67008a07d37dee380567d5eeb556ed127759e7/Proofs/TagSystem) | `ff67008a` | Proves the one-hot two-tag to cyclic-tag step simulation | Use as an independent specification only. The repository has no stated license; its Turing-machine to two-tag simulation is an explicit hypothesis. |
| [UniversalityDB](https://github.com/WolframInstitute/UniversalityDB/tree/d4383c47b5db3a3673a7d88472409eb1bd912ff0) | `d4383c47` | Catalogues the Wolfram universality chain | Not adopted: the catalogue records the same missing Turing-machine to two-tag theorem. |
| [DiagonaLean](https://github.com/DiagonaLean/DiagonaLean/tree/28ed8223dcfb389c8c1b655521099500b7bc53af) | `28ed8223` | Formalizes substantial HALT, MPCP, PCP, and matrix-mortality semantics | Not adopted. Its `ManyOneReduces` permits an arbitrary function, `SDecidable` permits an arbitrary Boolean characteristic function, and the HALT-to-MPCP tile compiler is declared `noncomputable`; these statements do not supply the executable many-one reduction required here. The general compiler also retains machine-normalization side conditions. |
| [cslib](https://github.com/leanprover/cslib/tree/0268c49a549b093bf865fc6c66c96ae5412494fe/Cslib/Computability) | `0268c49a` | Supplies finite-state Turing-machine and unlimited-register-machine semantics | Potential semantic library only. No universality or halting-noncomputability bridge was present at the audited revision. |
| [Jacob Weightman's tag-system branch](https://github.com/jacobdweightman/mathlib4/tree/ec3a5db58c8d2f7222116101980787788a5bfc36/Mathlib/Computability) | `ec3a5db5` | Develops tag-system semantics and elementary dynamics | Not adopted: it has no universality compiler and contains admitted declarations. |
| [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability/tree/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c) | `c7257b73` | Gives certified generic reductions through binary PCP | Proof blueprint only. It is Coq rather than Lean and its generic PCP instances do not preserve the four-generator bound. |
| [rule110-lean](https://github.com/novaspivack/rule110-lean/tree/cbbc170e48f254fcd822d10e759eecb4e359a943) | `cbbc170e` | Formalizes portions of Cook's Rule 110 simulation | Not adopted: its published status leaves the central simulation bridges as hypotheses and uses native evaluation certificates. |
| [dna-tiles](https://github.com/CharlesCNorton/dna-tiles/tree/0410cdf30e11da33678d9e1ae94c94cffbcc22ef) | `0410cdf3` | Defines Turing machines and cyclic tag systems in Rocq | Not adopted. Its claimed cyclic-tag completeness selects a trivially halting or looping system by classical excluded middle after asking whether the source machine halts. This proves an extensional existence statement, not a computable compiler. |

No audited public artifact closes either missing specialized edge: an executable universal
source-to-two-tag compiler, or Neary's cyclic-tag-to-restricted-binary-tag Table 2 compiler.
Accordingly, this project keeps mathlib's code-halting theorem, proves the two-tag-to-cyclic-tag
compiler independently, and formalizes the remaining translations locally. This is a search
result, not a claim that no unpublished or unindexed development exists.

## Mechanical Verification

```sh
./scripts/check.sh
```

The build treats warnings as errors, disables automatic implicit variables, enables mathlib's
strict syntax profile, runs every default environment linter, compares
`verification/axioms.txt` byte-for-byte, rejects proof escapes and strictness relaxations, runs
the typed finite falsifier, validates the HTML, checks reference-PDF identities, and reproduces
the manuscript PDF. The finite search independently checks bounded source words, compressed
coefficients, decoder coverage, and arbitrary four-matrix products. It is a transcription-error
detector, not part of the proof.
