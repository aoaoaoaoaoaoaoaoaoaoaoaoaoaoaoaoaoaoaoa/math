# Formalization Envelope

The Lean development now verifies the entire novel reduction from Neary's restricted binary
tag family to four-generator GPCP, a corrected binary five-pair PCP family, and the exact five
integer matrices. It does not assume Rote's terminal-tile statement.

For the logical foundation, kernel trust model, and remaining external theorem, see
[FOUNDATIONS.md](FOUNDATIONS.md).

## Files

| File | Checked content |
| --- | --- |
| `TagQueue.lean` | fixed-width tag steps; global history equation iff a lawful finite execution up to the first short queue |
| `NearyEncoding.lean` | Neary's four ordinary tiles; pulse parser; terminal equation iff tag halting; corrected PCP, GPCP, and mortality compositions |
| `MarkedTerminal.lean` | fresh-marker synchronization; primitive terminality; fixed-length binary recoding |
| `TernaryEncoding.lean` | nonzero ternary digits, concatenation, and injectivity |
| `PCPEncoding.lean` | the `3 × 3` word-pair morphism, equality entry, determinant, and triangularity |
| `TerminalTile.lean` | arbitrary rank-one chains, boundary nonvanishing, and raw-word fracture at every separator |
| `TerminalReduction.lean` | exact terminal scalar, rational and integer generators, multiplicative casting, and zero reflection |
| `TerminalSource.lean` | generic primitive extraction and fixed-right-boundary GPCP bridge |
| `AxiomAudit.lean` | reproducible `#print axioms` queries for every headline theorem |

## Source theorem

For deletion width `β`, body `q`, rules `b ↦ b` and `c ↦ q ++ [b]`, and initial queue
`q.drop (β−1) ++ [b]`, the central declaration is:

```text
terminal_match_iff_tagHaltsFrom
```

Under `2 < β`, `β−1 ≤ q.length`, and `β−1 ∣ q.length`, it proves:

```text
∃w over the four ordinary labels, upper(w) ++ 10^β = lower(w)
  ↔ the restricted tag system halts from its prescribed initial queue.
```

The forward proof does not assume intended simulation. `tileHistory_of_terminal_match` runs a
zero-gap automaton over an arbitrary lower product and forces its labels into blocks containing
one rule tile and exactly `β−1` erase tiles. The decoded equality becomes a queue-history
certificate. `tagHaltsFrom_of_history` proves by prefix cancellation that every such certificate
describes lawful tag steps, stopping immediately if an earlier short queue occurs.

The converse records actual deleted blocks. An invariant states that every reachable queue ends
in `b` and has length congruent to `1 mod (β−1)`. Hence a short queue is exactly `[b]`, which
closes the terminal equation.

`NearyArithmeticEnvelope` records the arithmetic envelope containing Neary's padded compiler
outputs:

```text
2 < β
q.length = (paddingRounds * β + 1) * (β−1).
```

This is intentionally not an exact characterization of Table 2 output: it omits `β=10p`, the
cyclic-tag instance, and the track constraints. The manuscript proves separately that a
computable congruent padding choice places Neary's undecidable compiler-output family inside
the envelope. Its `gpcp_solvable_iff_halts`, `gpcpPlus_solvable_iff_halts`,
`pcp_solvable_iff_halts`, and `mortality_iff_halts` theorems are the publication-facing
instance-level specializations.

## Corrected five-pair PCP

`MarkedTerminal.lean` appends a fresh delimiter to the fixed upper boundary and uses the pair

```text
(10^β #, #).
```

It then encodes `0`, `1`, and `#` by the two-bit words `00`, `01`, and `11`. The ordinary
upper words end in `1`; the ordinary lower words end in `0`; therefore every PCP solution uses
the distinguished tile. At its first occurrence, the fresh marker makes prefix comparability
equivalent to exact terminal matching. A primitive solution must stop there.

The resulting exact theorems are:

```text
nearyPCP_solvable_iff_tagHaltsFrom
nearyPCP_primitive_terminal
```

No quantitative long-block argument or classification of post-halt junk residuals remains.

## Exact five matrices

`nearyMortalityFamilyInt β q` has label type `Option NearyTile`. `NearyTile` has four
elements, so the full label type has exactly five. The four `some` labels emit the ordinary
ternary PCP matrices. The `none` label emits

```text
Ψ(10^β, ε) e₃ e₁ᵀ.
```

The raw mortality witness is an arbitrary nonempty word over all five labels. `fracture` splits
it at every exceptional occurrence. The proof covers zero, one, or arbitrarily many separators;
empty prefix, suffix, or internal blocks; adjacent separators; and arbitrary ordinary order.

The central equivalence is:

```text
nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom
```

The exact structure promises are checked separately:

```text
nearyMortality_ordinary_det_ne_zero
nearyMortality_ordinary_upperTriangular
nearyMortality_terminal_ne_zero
nearyMortality_terminal_rank_eq_one
neary_generator_count
neary_source_generator_count
neary_morphisms_nonerasing
```

The nonsingularity argument occurs over `ℚ`. Entrywise `ℤ → ℚ` casting is proved
multiplicative on the products in question and reflects zero, so no rational relaxation is
introduced.

## Mechanical checks

On 2026-07-21:

```text
$ ./scripts/check.sh
[integrity, Lean, axiom, proof-escape, Python, falsifier, HTML, and PDF checks pass]
```

The independent falsifier reports `20,272,272` arbitrary tile words, `56` terminal matches,
and `69` reconstructed halting witnesses. Frozen transcripts and exact revisions are in
[`verification/`](verification/README.md) and [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

There are no custom axioms, admitted statements, unsafe theorem declarations, or
`native_decide` proofs.

The finite scour is deliberately independent of Lean and exhausts small arbitrary label words,
including malformed orderings. It is only a falsifier, not part of the proof.

## Not yet machine-checked

- Neary's Lemma 9 / Table 2 compiler establishing undecidability of the admissible restricted
  tag family;
- computability and many-one-reduction bookkeeping from a mathlib machine-halting predicate;
- CHHN's dimension and generator trades;
- bibliographic novelty.

The first two items delimit “fully machine-checked undecidability.” They no longer delimit the
new mathematical argument: the malformed-path exclusion and every map from the restricted tag
source through the exact five matrices are formalized.
