# M₃(4) Terminal-Fork Core and Persistent-Guard Audit

**Date:** 2026-08-31
**Author and formalizer:** GPT-5.6 Sol
**Human role:** elicited by @eternalism_4eva
**Baseline:** `f7b6021` on `wave3-m34-transverse`
**Formal owners:**
[`TerminalForkCore.lean`](../MatrixMortality/TerminalForkCore.lean) and
[`MixedBranchingPersistentGuard.lean`](../MatrixMortality/MixedBranchingPersistentGuard.lean)

## Verdict

`G3-O35` used an incidental common quotient to expose a necessary general phenomenon: exact
three-state recognition of the `bcbc` source forces the complete flat/nested terminal-fork orbit
into a nonzero proper common invariant subspace of dimension one or two.

That constraint does not force both data controls to be singular. An even persistent guard can
make data `b` full-rank while preserving the complete all-word zero language of the exact
`bcbcbb` recognizer. A live uniform architecture may therefore use one singular syntax gate and
one full-rank persistent transition. It must still solve the source-computable terminal geometry.

## Exact G3-O35 Hypotheses

The failed separated carrier had five relevant properties:

1. The `bcbc` terminal language contains `A{F₀,F₁}*T`, where `A` is fixed and `F₀,F₁`
   are the flat and nested null-block products.
2. Both data controls factor through one two-dimensional input quotient, so every fork block
   acts on the same quotient.
3. The selected flat quotient is invertible.
4. The flat/nested quotient commutator is nonsingular for every nonzero source.
5. The prefixed row and toggled column admit explicit nonterminal false-zero witnesses if either
   projected boundary vector vanishes.

Only item 1 and boundary correctness survive in the general theorem. Items 2--4 made the fork
core irreducible and therefore forced a contradiction. A lawful candidate must make the fork
orbit reducible on purpose.

## Universal Fork Core

For arbitrary rational three-state controls, row `λ`, and column `γ`, put

```text
r = λ A,                 q = Tγ,
W = spanℚ {F_w q | w ∈ {0,1}*}.
```

All fork words are paired zeros. Same-zero correctness therefore gives `rW=0`, while prepending
one bit gives `F₀W⊆W` and `F₁W⊆W`. If `q=0`, the raw toggle is a false zero. If `r=0`,
the fixed prefix without its terminal toggle is a false zero. Hence `W≠0` and `W⊊ℚ³`, so
`dim W∈{1,2}`.

This is the precise joint `M₂(3)` seam. When both fork blocks are invertible, their restrictions
to `W` are automorphisms. The two-dimensional branch is a positive `GL₂(ℚ)` orbit selected by
one scalar boundary; the remaining coordinate can only enforce entry, exit, or malformed-word
rejection. The theorem does not reduce the complete raw three-letter action to one `M₂(3)`
instance.

## Persistent-Guard Escape

The exact integral `bcbcbb` recognizer has refreshed guard equations

```text
g(bw) = 2k(w)+1,
g(cw) = 2k(w)-2K,
```

where `k` is the persistent carry and `K=216186449` is the accepting carry. Replace the first
equation by

```text
g_m(bw) = m g_m(w)+2k(w)+1
```

and leave data `c`, the carry, toggle, row, and column unchanged. If `m` is even, every
`b`-headed guard remains odd. Data `c` ignores the incoming guard and retains exactly the old
acceptance equation. Thus `g_m(w)=0 ⇔ g(w)=0` for every raw word, and the existing checked
all-word converse transfers without a new grammar audit.

The modified matrix is

```text
D_b(m) = [m  2        1]
         [0  5  3703455]
         [0  0        1],

det D_b(m)=5m.
```

For every nonzero even `m`, data `b` has rational rank three and no kernel. The unchanged data
`c` remains a singular refresh. This removes the common-kernel hypothesis while retaining a
complete free-monoid zero equivalence.

## Scope

The fork-core theorem fixes the `bcbc` source and constrains its composite null blocks, not each
raw generator. The persistent-guard family fixes `bcbcbb`; it is not computable uniformization
over arbitrary Neary bodies. Its carry remains within the expanding-affine class whose finite
target sections are decidable by `G3-O04`.

The result therefore changes the live architecture but not the master verdict. A successor must
combine a singular all-word gate with a source-dependent one- or two-dimensional terminal core
whose target geometry is not a computably finite affine section.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| Every exact `bcbc` recognizer has a nonzero proper invariant fork carrier | promotion | Lean span and boundary theorems |
| That carrier has dimension one or two | promotion | Lean finrank theorem |
| Generic irreducible three-state fork actions are impossible | promotion | immediate consequence of the carrier theorem |
| Even persistent memory preserves the exact `bcbcbb` zero language | promotion | Lean all-word equivalence |
| Nonzero memory makes data `b` full-rank over `ℚ` | promotion | Lean determinant and rank certificates |
| Both data controls must be singular or share a kernel | rejected | persistent-guard counterexample |
| The construction is source-uniform | rejected | accepting carry remains fixed-body data |
| `M₃(4)` follows | rejected | arbitrary-body terminal geometry remains open |

## Formal Validation

Both formal owners compile warning-free under the repository toolchain and pass the default
environment linter. Publication-facing declarations are listed in
[`AxiomAudit.lean`](../AxiomAudit.lean); their transitive axiom outputs contain only the reviewed
standard axioms. No proof aperture, project axiom, unsafe declaration, linter suppression, or
external certificate is introduced.

## Master Delta

```text
MASTER VERDICT: M₃(4) remains open.
CUT: every exact bcbc recognizer has a 1D/2D invariant terminal-fork core.
ESCAPE: bcbcbb admits an exact even-memory family with full-rank data b and singular data c.
NO-GO RETIRED: common kernel and two singular data maps are not universal necessities.
LIVE ARCHITECTURE: singular all-word gate + source-dependent GL₁/GL₂ terminal core.
JOINT SEAM: the invertible 2D core is the positive M₂(3) projective-incidence problem.
```
