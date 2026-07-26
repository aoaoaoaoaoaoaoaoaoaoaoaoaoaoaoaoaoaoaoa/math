# Neary (2015)

**Citation.** Turlough Neary, “Undecidability in Binary Tag Systems and the Post
Correspondence Problem for Five Pairs of Words,” *32nd Symposium on Theoretical Aspects of
Computer Science (STACS 2015)*, LIPIcs 30, pp. 649–661, 2015.

- DOI: https://doi.org/10.4230/LIPIcs.STACS.2015.649
- Canonical source: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2015.649
- Local PDF: `neary-2015-five-pair-pcp.pdf`
- Retrieved: 2026-07-21
- SHA-256: `e932007062b58b88bd0598881ad8b3c56c878b5940b142deacbdb058a0774146`

## Results used

Lemma 9 proves halting undecidable for binary tag systems with deletion width `β`, rules
`b→b` and `c→u₀...uₗb`, and prescribed input `u_{β−1}u_β...uₗb`. Its Table 2 compiler has
`β=10p`; the whole `c`-appendant has length `βs`, with a freely enlargeable padding parameter.
Theorem 11 invokes the freedom to choose any sufficiently large `s`, takes
`s=x(β−1)+1`, and gives the four ordinary word pairs used in this project. An explicit
computable choice is obtained from

```text
B = max(11(n+p)+β−2, 11p, 11r, 1)
x = ceil((B−1)/(β−1)).
```

Every variable exponent in Table 2 is then nonnegative.

The exact arithmetic seam is:

```text
body = u₀...uₗ
initial = body.drop (β−1) ++ [b]
body.length = β[x(β−1)+1]−1 = (xβ+1)(β−1).
```

These facts place the compiler outputs inside `NearyArithmeticEnvelope`; that structure is a
strictly broader arithmetic class, not an exact model of Table 2. The project uses Table 2 and
the displayed ordinary pairs as construction sources, but defines the compiler locally and
proves its universality and fixed-boundary soundness in Lean. Lemma 9 is therefore provenance,
not an imported proof premise. Corollary 12 records the conventional six-generator `3 × 3`
mortality bound.

## Audit notes

The published proof's exclusion of premature uses of pair 5 is defective: it asserts that the tag
word `u` has no adjacent `c` symbols, although its own examples contradict this. Accordingly,
Neary's Theorem 11 converse is not used. The present proof instead shows directly, for arbitrary
words over the first four labels, that `U(w)10^β=V(w)` is equivalent to tag halting; it then adds
a fresh synchronizing marker to obtain a corrected fifth pair.

The local formalization reconstructs Table 2 with an explicit padding function, proves protected
forward execution and the arbitrary-execution converse, and composes it with fixed universal
machine, two-tag, and cyclic-tag compilers. Lean derives the final computable many-one reductions
to binary `GPCP(4)` and `M₃(5)` without assuming Lemma 9.
