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
  ↔ mortality of the emitted four 4 × 4 integer matrices.
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

## Modules

| File | Responsibility |
| --- | --- |
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

Thus both source-to-matrix equivalences and a substantial proper prefix of the universality
compiler are machine-checked. The exact encoded `M₄(4)` result currently ends at
`nearyMortality44_mortal_iff_tagHaltsFrom`; the final no-decider theorem is conditional on a
computable source reduction through `mortality44_not_computable_of_reduction`. The published
undecidability conclusion still uses Neary's peer-reviewed Lemma 9 at that remaining external
boundary. CHHN's generator-dimension trades and bibliographic priority claims are also external
to Lean and are not dependencies of the direct `M₄(4)` compiler.

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
