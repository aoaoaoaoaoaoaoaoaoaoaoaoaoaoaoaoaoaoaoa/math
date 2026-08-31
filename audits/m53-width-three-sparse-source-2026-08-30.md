# Width-Three Sparse-Source Audit

## Target

The scheduled five-state route to `M₅(3)` needs a primitive-recursive body family `q(e)` with
even length at least two and

```text
TagHaltsFrom 3 (b ↦ b, c ↦ q(e)b) (q(e).drop 2 · b) ↔ CodeHalts(e).
```

The production body and initial queue are coupled. A fixed width-three machine with an
independent input compiler does not supply this theorem.

## Sparse-Body Theorem

Lean proves that the coupled queue halts for every body containing at most one `c`; no length or
parity hypothesis is needed. For a one-`c` body, write

```text
q = b^p c b^s,
queue = b^i c b^j,
K = p + 3s + 1,
Δ = 2(i + 3j) - 3K.
```

A leading `b` step sends `(i,j)` to `(i-3,j+1)` and preserves `i+3j`. If `i=1` or `i=2`, the
next step deletes the unique `c` and leaves an all-`b` queue. If `i=0` and `j≥2`, a `c` step
sends

```text
(0,j) ↦ (j-2+p,s+1)
```

and every surviving continuation satisfies `Δ ↦ Δ/3`. The coupled initial queue has
`i+3j=K`, hence `Δ=-K`. Since `K>0`, infinitely many surviving `c` firings would make a
nonzero integer divisible by every power of three. The Lean proof makes this constructive by
strong induction on the positive defect magnitude, nested with strong induction on the leading
`b` count.

Bodies with no `c` and the cases where the initial `.drop 2` removes the unique `c` reduce
directly to the all-`b` descent.

## Source Consequence

For any family satisfying the exact halting equivalence, some nonhalting source code must map to
a body containing at least two `c` letters. This follows from mathlib's noncomputability theorem
for `CodeHalts`: if every code halted, the constant-true characteristic function would decide
it. The conclusion is only a necessary condition. It does not assert that the two-`c` stratum is
universal or undecidable.

The result excludes sparse retimings of Neary's variable-width source. Computation already
appears at the next stratum: two-`c` bodies include both terminating examples and explicit
periodic examples, so the defect proof cannot extend merely by replacing uniqueness with a
bounded count.

## Verification

The declarations are in
[`WidthThreeSparseBody.lean`](../MatrixMortality/WidthThreeSparseBody.lean):

- `sparseBody_coupled_halts`;
- `coupled_halts_of_count_c_le_one`;
- `exact_source_has_body_with_two_c`.

The proof uses only the repository's tag-step semantics and mathlib's formal code-halting
theorem. It introduces no axiom, external declaration, proof aperture, or literature premise.

## Literature Boundary

De Mol's binary two-tag theorem also cites Wang's elementary decidable regime in which every
appendant has length at most the deletion width. In the present notation that only handles
`|q|≤2`. The formal sparse-body theorem applies at every body length. No inspected source states
this coupled one-`c` result; no priority claim is made without a broader search.
