# Adversarial audit: paired-role compression and `M₄(4)`

**Audit date:** 2026-07-22  
**Audited formalization revision:** `b99e6590225fca81b50a6837adbab97073321505`  
**Integration disposition:** accepted after the repairs recorded below

## Verdict

The core result survives adversarial review. No counterexample was found to:

- the explicit four-dimensional quotient realization;
- the suffix-controlled decoder on arbitrary control words;
- decoder surjectivity onto all four-role words;
- the scalar coefficient identity;
- the rank-one mortality converse for arbitrary products;
- the integer-to-rational zero reflection;
- the stated common-column, permutation, nonzero, and rank-one promises.

The checked instance-level equivalence is:

```text
restricted tag halting
  ↔ scalar zero reachability for three 4 × 4 integer matrices
  ↔ mortality for four 4 × 4 integer matrices.
```

The unconditional mathematical undecidability theorem imports Neary's peer-reviewed
restricted binary-tag theorem and the padding corollary derived from its construction. The
final computable many-one reduction from a standard halting problem is not yet formalized.

## Repairs

The audit found two false statements in prose:

1. The control family was described as singular. Only the two data controls are singular; the
   toggle is an invertible permutation matrix.
2. A Lean docstring described the toggle as swapping coordinates one and three. It swaps
   zero-based `Fin 4` indices `1` and `3`, hence one-based coordinates two and four.

Both statements were corrected. The exposition was also hardened to:

- state the generic compression theorem over a finite-dimensional vector space over a field;
- distinguish the abstract quotient theorem from the explicit realization checked by Lean;
- state the Neary padding corollary separately from Lemma 9;
- define scalar zero reachability and its nonempty-product convention;
- explain the multiplication orientation that forces suffix-controlled decoding;
- replace unqualified antichain language with dated Pareto-minimal undecidability claims;
- qualify priority by the public-literature search date.

## Mathematical seam

Neary's Lemma 9 supplies undecidability for the required restricted binary-tag semantics. The
additional arithmetic hypotheses used by the checked compiler are obtained from the selectable
padding in Neary's construction. With `β = 10p` and

```text
s = x(β−1) + 1,
```

the body before the final `b` has length

```text
|q| = βs−1 = (xβ+1)(β−1).
```

Thus `β > 2`, `β−1 ≤ |q|`, and `β−1 ∣ |q|`. The padding parameter can be chosen computably
above the finitely many lower bounds in the construction. This corollary is not the bare wording
of Lemma 9 and is stated separately in the exposition.

## Formal scope

Lean checks the exact source-to-matrix instance compiler, not the complete undecidability chain.
In particular:

- the explicit `d = 3`, `r = 2` realization is checked;
- the arbitrary-word coefficient identity and surjectivity are checked;
- mortality uses nonempty words;
- empty role and toggle-only witnesses are excluded by `LC = μ ≠ 0`;
- every separator count and placement is checked;
- the integer matrices are mortal exactly when their rational casts are mortal;
- the separator is nonzero and has rank one over `ℚ`.

The abstract `2d−r` quotient theorem is paper mathematics rather than a separate Lean
declaration. Neary's universality compiler, the final no-decider wrapper, CHHN's frontier
propagation, and bibliographic priority remain external.

The transitive axiom snapshot for publication-facing declarations contains only:

```text
propext
Classical.choice
Quot.sound
```

The repository gate rejects admitted proofs, project axioms, unsafe or partial declarations,
native decision shortcuts, external declarations, implementation overrides, metaprogrammed proof
execution, and linter suppressions.

## Priority

To our knowledge, after searches through 2026-07-22, no prior public proof establishes `M₄(4)`
or scalar zero reachability for three common-first-column `4 × 4` integer matrices. CHHN's
closest established points are `M₅(4)` and structured `Z₅(3)`.

The rank-one scalar-to-mortality reduction, common-column structured instances, and quotient
linear algebra are prior art. The priority claim is limited to the paired-role compression,
total suffix decoder, common-column converse with singular data controls, and resulting numerical
points. It is a dated public-literature assessment, not a claim about unpublished work.

## Deferred work

The audit recommends a source-independent theorem characterizing rank-one scalar-to-mortality
conversion for generator families fixing a common anchor. This is a reusable refactoring, not a
condition of the present result. The complete formal no-decider theorem remains background
rectification work.
