# Proper False Inverse-Ray Audit

**Date:** 2026-08-31

**Author and formalizer:** GPT-5.6 Sol

**Human role:** elicited by @eternalism_4eva

**Baseline:** `8410388` on `wave3-m34-ucb`

**Salvage record:** `D2-O14`

## Verdict

Primitive height tending to infinity does not prune unguided inverse search,
even in a promised-empty free orbit whose source and target stabilizers are
both trivial.

Use the dilation and transverse parabolic from `D2-O05`:

```text
D(z)=5z,       U(z)=(-2z+3)/(-3z+4),       p=9/4.
```

Set

```text
r=11/5,       q=D⁻¹r=11/25.
```

The anchor `r` lies in the neutral gap outside both ping-pong chambers. Every
nonzero dilation power sends it into the dilation chamber, and every nonzero
transverse power sends it into the transverse chamber. The general ping-pong
base theorem therefore gives `Stab(r)={1}`.

The point `r` is outside the orbit of `p`. The identity misses it, while every
nonidentity word sends `p` into one of the strict chambers. Consequently `q`
is also outside the source orbit: a hit on `q` followed by `D` would hit `r`.
Since `q=D⁻¹r`, conjugation gives `Stab(q)={1}`.

The matrix

```text
g₀=[[-17,41],[-39,94]],       det(g₀)=1,
```

sends `[9:4]` to `[11:25]`. Lean proves that the represented subgroup misses
`g₀Stab(p)`. Together with the existing determinant-one source conjugation,
this is a cardinality-zero `UCB₂({5})` instance; all matrices lie in
`PGL₂(ℤ[1/5])`.

## The False Ray

Unguided inverse search can repeatedly choose `D⁻¹` from `q`. At depth `n`,

```text
D⁻ⁿq = 11/(25·5ⁿ),
vₙ=(11,5^(n+2)),
height(vₙ)=5^(n+2).
```

Lean proves that the abstract prefixes `D⁻ⁿ` are pairwise distinct, `vₙ` is
primitive, its projectivization equals the displayed orbit point, and its
exact height tends to infinity.

The ray is false because it ignores chamber direction. The target lies in the
lower dilation chamber, which records a negative outer dilation exponent; a
chamber-directed parser removes that exponent by applying `D`, reaches the
neutral anchor, and rejects. Unguided application of `D⁻¹` moves in the
opposite direction forever.

## Consequence

`D2-O13` proves that a trivial-stabilizer survivor must eventually leave every
fixed height cube. This example satisfies that conclusion exactly and remains
irrelevant to reachability. Proper height escape is therefore necessary but
not sufficient. A viable inverse algorithm must couple height to a lawful
direction: ping-pong chamber, real orientation, `S`-adic valuation sign, or an
equivalent complete normal-form rule.

This does not refute chamber-directed search. It isolates why direction cannot
be omitted.

## Formalization

`TransverseDilationOrbit.lean` adds:

1. a reusable ping-pong base theorem and stabilizer criterion;
2. the exact anchor/target chamber and orbit exclusions;
3. a determinant-one false-target transporter and empty-coset theorem;
4. trivial target stabilizer by conjugation;
5. distinct inverse-dilation prefixes and their exact rational actions;
6. primitive pairs `(11,5^(n+2))`; and
7. exact height and `atTop` convergence.

## Verification

The following checks pass in the isolated worktree:

```text
lake build MatrixMortality.TransverseDilationOrbit
default namespace linter: no findings
Lean LSP diagnostics: 0 errors, 0 warnings, 0 information, 0 hints
```

Every publication-facing theorem is listed in `AxiomAudit.lean` and depends
only on the reviewed Mathlib axioms. No project axiom, proof aperture, warning
suppression, reference PDF, or external literature premise was added.

## Claim Classification

| Claim | Classification | Evidence |
| --- | --- | --- |
| The anchor and false target have trivial represented stabilizers | promotion | Lean-checked ping-pong and conjugation |
| The false target is outside the source orbit and its transporter coset is empty | promotion | Lean-checked chamber exclusion and exact determinant-one transporter |
| `D⁻ⁿq` has primitive pair `(11,5^(n+2))` | promotion | Lean-checked exact projectivization and coprimality |
| The false-ray prefixes are distinct and their heights tend to infinity | promotion | Lean-checked exponent injectivity and `atTop` convergence |
| Proper primitive-height escape alone prunes all false inverse branches | rejected | the explicit ray is proper and irrelevant |
| Chamber-directed inverse search fails on this example | rejected | the false ray deliberately moves against the chamber sign |
| General `UCB₂(S)` is decidable | open | completeness of a directional parser is not proved |

## Master Delta

```text
MASTER VERDICT: M₃(4), M₂(3), and GPCP(3) remain open.
REMOVED: proper height escape as a standalone pruning criterion for unguided
         inverse search.
ADDED:   one promised-empty trivial-endpoint-stabilizer instance with an
         explicit false inverse ray of exact height 5^(n+2).
REMAINS: build and prove complete a chamber/place-directed inverse parser.
```

## Artifacts

- [`TransverseDilationOrbit.lean`](../MatrixMortality/TransverseDilationOrbit.lean)
- [`D2-O14`](../SALVAGE.md#d2-o14-proper-false-inverse-ray)
