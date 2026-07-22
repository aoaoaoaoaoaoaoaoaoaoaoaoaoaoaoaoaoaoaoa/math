# Formal Foundations and Trust Boundary

## What Lean has proved

The formal development proves the novel mathematical bridge for every admissible restricted
tag source, not merely for an intended computation trace:

```text
four-tile terminal equation
  ↔ restricted tag halting
  ↔ corrected fresh-marker five-pair PCP solvability
  ↔ mortality of the exact five emitted 3 × 3 integer matrices.
```

The forward source proof accepts an arbitrary word over the four tile labels. A finite-state
zero-run parser forces it into deletion-width blocks; a generic queue-history theorem then
recovers lawful tag steps and stops at the first short queue. This is the formal closure of the
malformed-residual hole found in the Neary–Rote argument.

The development also proves primitive terminality of the new fifth pair, binary recoding,
matrix integrality, the arbitrary-product mortality converse, nonsingularity and upper
triangularity of the four ordinary matrices, and exact rational rank one of the fifth.

## The logical foundation

Lean checks propositions by reducing them to terms in a dependent type theory descended from
the Calculus of Inductive Constructions. The important ingredients here are:

- dependent function types and ordinary inductive types;
- an impredicative, proof-irrelevant universe `Prop`;
- quotient types;
- propositional extensionality;
- classical choice.

For every principal theorem, `#print axioms` reports exactly:

```text
propext
Classical.choice
Quot.sound
```

`propext` identifies logically equivalent propositions. `Classical.choice` permits selection
from a proof that a type is inhabited and entails ordinary classical reasoning such as excluded
middle. `Quot.sound` identifies representatives related by a quotient relation. These are the
standard classical foundations used throughout mathlib; the project adds no axiom.

Lean cannot prove the consistency of this foundation from within itself. As with ordinary
classical mathematics, consistency is a metamathematical assumption. Nothing in this project
uses a large-cardinal axiom, an oracle, probabilistic reasoning, floating-point arithmetic, or an
unverified computer-algebra result.

## What mathlib contributes

Mathlib supplies definitions and previously proved lemmas for lists, natural numbers, matrices,
linear maps, determinants, ranks, finite types, and elementary algebra. It is a library, not a
second proof engine and not an additional axiom set. Its declarations carry proof terms checked
by the same Lean kernel as project theorems.

Tactics such as `simp` and `omega` are proof-producing metaprograms. They may search or compute,
but the kernel checks the term they return. A tactic bug normally causes failure or an invalid
term rejected by the kernel; it cannot decree a proposition true. The development does not use
`native_decide`, unsafe theorem declarations, or external proof certificates. Its small uses of
`decide` are evaluated by kernel reduction.

The project pins both Lean and mathlib to `v4.12.0`; `lake-manifest.json` fixes the resolved
dependency revisions. A clean build therefore reconstructs the checked environment from a
specific source graph.

## The actual trusted computing base

Formal proof narrows trust; it does not abolish it. Operationally we trust:

1. Lean 4's small kernel implementation to implement its typing rules correctly.
2. The Lean executable, runtime, operating system, and hardware not to corrupt the checked
   declarations or report a false successful exit.
3. The project source and pinned dependency sources to be the files we intend to check.
4. The mathematical specification to express the intended matrix mortality and tag-system
   problems. A kernel can verify a theorem about the wrong definition perfectly.

The parser, elaborator, simplifier, arithmetic tactics, and most of mathlib are outside the
logical trusted core because their output is kernel-checked. For maximal assurance one can
rebuild with an independently compiled Lean toolchain, compare source hashes, or export the
proofs to another checker. Such measures defend against implementation or supply-chain faults,
not against a gap in the formal proof term.

## The remaining external theorem

One mathematical dependency is not yet represented by a Lean proof: Neary's Lemma 9, which
computably translates an arbitrary Turing-machine computation, through a cyclic tag system,
into the restricted binary tag family used here and proves its halting problem undecidable.

The formal source theorem covers that paper's outputs. Neary has deletion width `β=10p`, a
whole `c`-appendant `body ++ [b]` of length `βs`, and initial queue
`body.drop (β−1) ++ [b]`. For a computable bound `B` exceeding every lower bound in Table 2,
choose `x=ceil((B−1)/(β−1))` and `s=x(β−1)+1`. This lies within Neary's freedom to take `s`
sufficiently large and gives

```text
body.length = (xβ + 1)(β−1),
```

which is precisely `NearyArithmeticEnvelope.body_length`. The envelope is strictly broader
than the compiler-output family: it deliberately forgets `β=10p`, the cyclic-tag instance,
and the Table 2 track constraints. The manuscript proves that the actual outputs inhabit it.
Thus the unformalized seam is the published universality compiler, not an identification
between its output and our theorem.

Consequently two claims must remain distinct:

- **Mathematical theorem:** combining the checked equivalence with Neary's peer-reviewed
  Lemma 9 proves `GPCP(4)` and `M₃(5)` undecidable without a conjectural premise.
- **Fully machine-checked theorem:** Lean currently proves the complete novel compiler for
  every source instance, but does not derive source undecidability from mathlib's halting
  theorem.

Closing the latter gap requires formalizing Neary's Table 2 cyclic-tag-to-binary-tag compiler
and its computability, or replacing it with a simpler formally universal restricted tag source.
Declaring Lemma 9 as a Lean axiom would make an unconditional-looking theorem, but would add
no assurance and is deliberately rejected.

The CHHN dimension trades and bibliographic novelty claims are likewise external. They do not
affect the correctness of the exact source-to-five-matrix equivalence.

## Reproduction

From the project root:

```sh
./scripts/check.sh
```

This checks the artifact and bibliography hashes; rebuilds Lean with warnings fatal and
automatic implicits disabled; runs every default mathlib environment linter; compares the exact
transitive axiom snapshot; rejects suppressions and proof escapes; runs the independently typed
finite falsifier; validates the HTML; and rebuilds the manuscript byte-for-byte. See
[REPRODUCIBILITY.md](REPRODUCIBILITY.md). The finite search is useful for detecting
transcription errors but is not evidence from which the universal theorem is inferred.

## Theorem map

| Mathematical claim | Lean declaration |
| --- | --- |
| Global history equation yields a lawful terminating run | `tagHaltsFrom_of_history` |
| Terminal equality forces exact deletion blocks | `tileHistory_of_terminal_match` |
| Four-tile equation iff restricted tag halting | `terminal_match_iff_tagHaltsFrom` |
| Corrected five-pair PCP iff tag halting | `nearyPCP_solvable_iff_tagHaltsFrom` |
| Every primitive corrected PCP solution ends in tile five | `nearyPCP_primitive_terminal` |
| Four-generator GPCP iff tag halting | `nearyGPCP_solvable_iff_tagHaltsFrom` |
| Nonempty-witness four-generator GPCP iff tag halting | `nearyGPCPPlus_solvable_iff_tagHaltsFrom` |
| Exact five integer matrices mortal iff tag halting | `nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom` |
| Arithmetic-envelope specialization | `NearyArithmeticEnvelope.mortality_iff_halts` |
| Four source labels and nonerasing images | `neary_source_generator_count`, `neary_morphisms_nonerasing` |
| Four ordinary matrices are nonsingular and triangular | `nearyMortality_ordinary_det_ne_zero`, `nearyMortality_ordinary_upperTriangular` |
| Exceptional matrix is nonzero and rational rank one | `nearyMortality_terminal_ne_zero`, `nearyMortality_terminal_rank_eq_one` |
