# Square-Root Boundary-Saturation Audit

Date: 2026-08-08

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

Master: undecidability of mortality for four 3 × 3 integer matrices, M₃(4)

External attack: [shared Pro conversation](https://chatgpt.com/share/6a77e215-0a94-83ea-82e1-0731c81e0a8e)

## Verdict

The report closes the square-root completion requested at G3-M02. Every square root of a
nondegenerate rank-one separator scales both separator boundary vectors by the same nonzero
scalar. Its scalar zero language is therefore invariant under insertion or deletion of one
distinguished letter at either word boundary. The native Neary zero language has the opposite
property: every terminal match begins with R_c, so no word prefixed by R_b is a zero.

This is a zero-set obstruction in arbitrary dimension. It does not preserve coefficient values,
assume a rank for the square root, or constrain the other generators.

## Boundary Eigenvectors

Let K be a field, let u be a column and vᵀ a row with

    κ=vᵀu ≠ 0,

and suppose

    P²=uvᵀ.

Since P commutes with P²,

    P(uvᵀ)=(uvᵀ)P.

Applying both sides to u gives

    κPu=(vᵀPu)u.

Thus Pu=σu for some scalar σ. Applying P again and using P²u=κu gives

    σ²=κ,

so σ is nonzero. Substitution into the matrix commutation identity then gives

    vᵀP=σvᵀ.

Lean proves the complete statement as
SquareRootPunctuation.squareRoot_boundary_eigenvectors, including σ²=κ.

For arbitrary intervening matrices,

    G(w)=vᵀH_wu

therefore satisfies

    G(Pw)=σG(w),
    G(wP)=σG(w).

Lean records both zero equivalences as squareRoot_coefficient_cons_zero_iff and
squareRoot_coefficient_append_zero_iff. The theorem quantifies over every field, dimension,
ordinary alphabet, and ordinary generator family.

## Native Boundary Asymmetry

Lean now factors the semantic equation used in the existing arbitrary-word converse into a
public theorem:

    consumed(first::history) b
      = c · body(first.head) · b · produced(history).

Taking first letters forces first.head=c. Combined with the pulse theorem, this proves that every
arbitrary terminal-match word, not merely every intended execution, has the form

    R_c · tail.

Consequently every role word R_b w has nonzero side coefficient. This is checked as
SquareRootPunctuation.nearySide_ruleB_cons_ne_zero.

## Contradiction

Take any halting checked universal source and a terminal-match role word w. Replace each R_b in w
by the distinguished physical letter P and the other three roles by their ordinary physical
letters, obtaining x.

Pulse synchronization writes w as complete width-β blocks, each containing one rule followed by
β−1 erasers. Since β≥3, x is PP-free. Its first role is R_c, so Px is also PP-free.

Suppose a same-zero completion existed on the entire PP-free domain. Native zero of w would give

    G(x)=0.

Boundary saturation gives G(Px)=0. Same-zero reflection would then make R_b w a native zero,
contradicting the checked initial-role theorem.

Lean packages the exact logical contradiction as
SquareRootPunctuation.no_ruleB_squareRoot_sameZero_on_boundary_pair. Its hypotheses expose the
two square-free words, the physical decoder, native zero, and the proposed all-domain same-zero
law. The routine fact that every complete β≥3 terminal history supplies such a pair remains a
paper-level composition of the already checked stroke decomposition; no publication-facing
declaration silently claims that final list-syntax wrapper.

The displayed Neary root is merely one instance. The argument applies to every square root of
the same nondegenerate separator in every dimension.

## Scope

The result kills every architecture retaining all of:

- a nondegenerate rank-one square P²=uvᵀ;
- scalar readout vᵀH_wu;
- the complete PP-free fracture domain, including boundary P;
- direct identification P↦R_b.

Direct identification with D_b or D_c dies by the same initial R_c rigidity. Identification with
R_c is instead attacked at the right boundary: a complete history ends in an eraser, and
appending an uncompleted rule cannot be a pulse-normal terminal match. That symmetric extension
is not needed for the requested compiler and is not promoted here.

A punctuation construction using a semantic macro rather than one Neary role, a degenerate
separator with vᵀu=0, or a fracture language excluding boundary punctuation lies outside the
theorem. None currently supplies a mortality converse.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every nondegenerate rank-one square root scales both boundary vectors | promotion | Lean theorem squareRoot_boundary_eigenvectors |
| Initial and terminal punctuation preserve scalar vanishing | promotion | Lean theorems squareRoot_coefficient_cons_zero_iff and squareRoot_coefficient_append_zero_iff |
| Every arbitrary Neary terminal match begins with R_c | promotion | Lean theorem terminalMatch_starts_rule_c |
| Every R_b-prefixed native role word has nonzero coefficient | promotion | Lean theorem nearySide_ruleB_cons_ne_zero |
| The requested SS-free same-zero compiler cannot exist | promotion | Lean logical consumer plus audited stroke-syntax composition |
| Another choice of square root can evade the obstruction | rejected | the eigenvector theorem quantifies over every square root |
| Every conceivable punctuation architecture is impossible | rejected | macro, degenerate, and boundary-excluding grammars lie outside scope |
| M₃(4) follows | rejected | the direct punctuation leaf closes without solving the master |

## Master Delta

    MASTER VERDICT: still open.
    REMOVED: the complete square-root SS-free compiler leaf, including every transient-guard
             completion with S↦R_b and the same separator grammar.
    ADDED: a dimension-free boundary-saturation invariant and checked initial-role rigidity.
    REMAINS: source-uniform history-sensitive singular paired recognition; a genuine word-valued
             three-letter GPCP source or recoding; positive free cancellation after its own audit.

## Artifacts

- [SquareRootPunctuation.lean](../MatrixMortality/SquareRootPunctuation.lean)
- [NearyEncoding.lean](../MatrixMortality/NearyEncoding.lean)
