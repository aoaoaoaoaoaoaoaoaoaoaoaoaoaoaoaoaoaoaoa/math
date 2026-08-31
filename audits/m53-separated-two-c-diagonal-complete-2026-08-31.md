# Complete separated-two-c diagonal audit

Date: 2026-08-31

Auditor and formalizer: GPT-5.6 Sol

Human role: elicited by @eternalism_4eva

## Claim

For deletion width three, body `qₙ = bb c bⁿ c bⁿ`, output `b↦b`, `c↦qₙb`, and coupled
initial queue `qₙ.drop 2 · b`, every `n≡2 (mod 3)` source halts. The existing exact cycles for
`n>0` with `n mod 3≠2`, together with a direct cycle for `n=0`, prove that the source halts
exactly when `n≡2 (mod 3)`.

This audit closes only the diagonal family. It does not classify unequal separated bodies
`bᵖ c bʳ c bˢ`, arbitrary two-`c` bodies, or the full binary width-three source problem.

## Exact macro

The prior residue cuts reduce the final class to `n=27a+11`. Set

```text
A = 9a+4,    m = 12a+5,
B = c b^(3A-1) c b^(4A+1) c b^(3A-1) c.
```

The six-event entry and a head-clean prefix reach `B b^(82a+38)`. The context form of the
four-active-`c` macro is exact: if a suffix begins with `b^(r+2)`, then firing the leading block
moves the remaining `b^r`, the untouched suffix, and the two consumed unary letters ahead of
the two emitted copies. This accounts for the two-letter displacement hidden by the unary-tail
specialization of `MM-S43`.

After deleting head-clean prefixes, every live queue has one of two forms:

```text
O(T) = B b^T,
P(T) = B b^(39a+19) B b^T.
```

With `s=105a+49`, `q=129a+62`, and `x=T-s`, the exact normalized transitions are

```text
O: x≡0 ↦ O(x/3),       x≡2 ↦ P((x-q)/3),   x≡1 halts,
P: x≡0 ↦ P(x/3),       x≡1 ↦ O((x+q)/3),   x≡2 halts.
```

The off-head copies of `B` are not erased informally. Each normalization proves that its full
prefix has `b` at every deletion head, executes that prefix through the tag semantics, and
retains the next active block exactly.

## Termination

The live coordinate lies in the finite open interval

```text
−q < 2x < q.
```

All four branches preserve this interval. A live successor has at most one live predecessor:
idle images lie in its central third, while crossing images lie in the corresponding outer
third. The initial state is `O(−23a−11)`. It lies in the interval, but neither possible
predecessor lies there. A finite partial graph with unique predecessors is accessible from a
predecessor-free root: remove the root, observe that its successor becomes predecessor-free in
the smaller graph, and recurse on cardinality. Hence the initial macro orbit reaches a missing
residue, whose expanded queue has only `b` at deletion heads and drains.

## Formal verification

[`MatrixMortality/SeparatedTwoCResidueTwo.lean`](../MatrixMortality/SeparatedTwoCResidueTwo.lean)
checks the arbitrary-context block macro and the entry to `B b^(82a+38)`.
[`MatrixMortality/SeparatedTwoCDiagonal.lean`](../MatrixMortality/SeparatedTwoCDiagonal.lean)
checks:

- the finite centered state space and predecessor uniqueness;
- accessibility of every initial centered defect;
- all one-block and two-block queue transitions and terminal phases;
- halting for `n=27a+11`;
- the combined theorem for every `n≡2 (mod 3)`;
- the `n=0` cycle and the classification equivalence for every natural `n`.

The publication-facing declarations are included in `AxiomAudit.lean`. The canonical project
gate checks warnings, forbidden proof apertures, environment linters, and the reviewed axiom
snapshot.
